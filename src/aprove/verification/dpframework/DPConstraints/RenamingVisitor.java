package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.idp.*;

public class RenamingVisitor extends DPConstraintVisitor {
    TRSSubstitution subs;

    public RenamingVisitor(TRSSubstitution subs) {
        super();
        this.subs = subs;
    }

    @Override
    public Set<TRSVariable> caseQuantor(Set<TRSVariable> quantor) {
        Set<TRSVariable> nQuantor = new LinkedHashSet<TRSVariable>();
        for (TRSVariable v : quantor) {
            nQuantor.add((TRSVariable) this.subs.substitute(v));
        }
        return nQuantor;
    }

    @Override
    public TRSVisitable casePredicate(Predicate predicate) {
        return predicate.applySubstitution(this.subs, false);
    }

    @Override
    public TRSVisitable caseReducesTo(ReducesTo reducesTo) {
        return reducesTo.applySubstitution(this.subs, false);
    }

    @Override
    public TRSVisitable caseUsableAtom(UsableAtom usa) {
        return usa.applySubstitution(this.subs, false);
    }

    @Override
    public boolean guardQuantor(Implication implication) {
        return true;
    }

}
