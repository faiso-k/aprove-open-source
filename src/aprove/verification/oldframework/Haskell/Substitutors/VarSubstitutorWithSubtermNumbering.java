package aprove.verification.oldframework.Haskell.Substitutors;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;

public class VarSubstitutorWithSubtermNumbering extends VarSubstitutor {


    public VarSubstitutorWithSubtermNumbering(HaskellSubstitution subs) {
        super(subs);
    }

    @Override
    public HaskellObject caseCons(Cons cons) {
        cons.setSubtermNumber(this.subs.getNewSubtermIDMax());
        this.subs.incSubtermIDMax();
        return cons;
    }

    @Override
    public HaskellObject caseApply(Apply apply) {
        apply.setSubtermNumber(this.subs.getNewSubtermIDMax());
        this.subs.incSubtermIDMax();
        return apply;
    }

    @Override
    public HaskellObject caseVar(Var var) {
        var.setSubtermNumber(this.subs.getNewSubtermIDMax());
        this.subs.incSubtermIDMax();
        return super.caseVar(var);
    }

}
