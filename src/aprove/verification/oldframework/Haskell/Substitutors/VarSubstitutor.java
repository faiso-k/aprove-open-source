package aprove.verification.oldframework.Haskell.Substitutors;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

/**
 * replaces variables by refering to a substitution
 * it considers quantors of typeschema
 * the VarSubstitutor is used by the method applyTo of Substitutions
 */
public class VarSubstitutor extends HaskellVisitor{
    Quantor quantor;
    HaskellSubstitution subs;

    public VarSubstitutor(HaskellSubstitution subs){
        this.subs = subs;
        this.quantor = null;
    }

    @Override
    public HaskellObject caseVar(Var var) {
        HaskellSym sym = var.getSymbol();
        if (this.quantor != null) {
            if (this.quantor.contains(sym)) {
                return var;
            }
        }
        HaskellObject rep = this.subs.get(sym);
        if (rep != null) {
            return Copy.deep(rep);
        } else {
            return var;
        }
    }

    @Override
    public void fcaseTypeSchema(TypeSchema ts){
        this.quantor = ts.getQuantor();
    //subs.constraintCollect();
    }

    @Override
    public HaskellObject caseTypeSchema(TypeSchema ts){
        //subs.constraintTransferTo(ts);
        this.quantor = null;
        return ts;
    }

    @Override
    public boolean guardMemberTypeSchemaClassConstraint(MemberTypeSchema ho) { return true; }


}
