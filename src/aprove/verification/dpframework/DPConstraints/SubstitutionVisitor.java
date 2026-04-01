package aprove.verification.dpframework.DPConstraints;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.idp.*;

public class SubstitutionVisitor extends DPConstraintVisitor {

    TRSSubstitution subs;
    private boolean idpMode;

    public SubstitutionVisitor(TRSSubstitution subs, boolean idpMode) {
        super();
        this.subs = subs;
        this.idpMode = idpMode;
    }

    @Override
    public TRSVisitable caseImplication(Implication implication) {
        return super.caseImplication(implication);
    }

    @Override
    public TRSVisitable casePredicate(Predicate predicate) {
        return predicate.applySubstitution(this.subs, this.idpMode);
    }

    @Override
    public TRSVisitable caseReducesTo(ReducesTo reducesTo) {
        return reducesTo.applySubstitution(this.subs, this.idpMode);
    }

    @Override
    public TRSVisitable caseUsableAtom(UsableAtom usa) {
        return usa.applySubstitution(this.subs, this.idpMode);
    }

}
