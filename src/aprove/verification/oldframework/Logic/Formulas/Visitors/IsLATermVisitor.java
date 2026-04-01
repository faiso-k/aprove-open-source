package aprove.verification.oldframework.Logic.Formulas.Visitors;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * A LA term is
 *   - a variable of sort Nat
 *   - the term Zero
 *   - a term succ( t_1 ) where t_1 is a LA term
 *   - a term plus( t_1, t_2 ) where t_1 and t_2 are LA terms
 *
 * @author dickmeis
 * @version $Id$
 */

public class IsLATermVisitor implements FineGrainedTermVisitor<Boolean> {

    LAProgramProperties laProgramProperties;

    private IsLATermVisitor(LAProgramProperties laProgramProperties){
        this.laProgramProperties = laProgramProperties;
    }

    public static boolean apply(AlgebraTerm term, LAProgramProperties laProgramProperties) {
        IsLATermVisitor isLATermVisitor = new IsLATermVisitor(laProgramProperties);
        return term.apply(isLATermVisitor);
    }

    @Override
    public Boolean caseConstructorApp(ConstructorApp cterm) {
        ConstructorSymbol cs = cterm.getConstructorSymbol();

        if(cs.equals(this.laProgramProperties.csZero)){
            // do not abstract from numbers
            return true;
        }
        else if(cs.equals(this.laProgramProperties.csSucc)){
            Boolean subTermIsLA = cterm.getArgument(0).apply(this);
            if(subTermIsLA){
                return true;
            }
        }

        return false;
    }

    @Override
    public Boolean caseDefFunctionApp(DefFunctionApp fterm) {
        SyntacticFunctionSymbol fs = fterm.getFunctionSymbol();

        if (fs.equals(this.laProgramProperties.fsPlus)){
            Boolean subTerm0IsLA = fterm.getArgument(0).apply(this);

            Boolean subTerm1IsLA = fterm.getArgument(1).apply(this);

            return subTerm0IsLA && subTerm1IsLA;
        }

        return false;
    }

    @Override
    public Boolean caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {
        return false;
    }

    @Override
    public Boolean caseVariable(AlgebraVariable v) {
        if (v.getSort().equals(this.laProgramProperties.sortNat)){
            return true;
        }
        else{
            return false;
        }
    }

}
