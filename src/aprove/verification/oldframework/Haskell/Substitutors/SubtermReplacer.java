package aprove.verification.oldframework.Haskell.Substitutors;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Utility.*;

public class SubtermReplacer extends HaskellVisitor {

    HaskellObject newSubterm;
    int subtermID;

    public SubtermReplacer(HaskellObject newSubterm, int subtermID) {
        this.newSubterm = newSubterm;
        this.subtermID = subtermID;
    }

    private HaskellObject doReplaceOnSameID(BasicTerm t) {
        //System.out.println(t.getSubtermNumber()+":"+t);
        if (t.getSubtermNumber() == this.subtermID) {
            return Copy.deep(this.newSubterm);
        }
        else {
            return t;
        }
    }

    @Override
    public HaskellObject caseCons(Cons cons) {
        return this.doReplaceOnSameID(cons);
    }

    @Override
    public HaskellObject caseApply(Apply apply) {
        return this.doReplaceOnSameID(apply);
    }

    @Override
    public HaskellObject caseVar(Var var) {
        return this.doReplaceOnSameID(var);
    }

}
