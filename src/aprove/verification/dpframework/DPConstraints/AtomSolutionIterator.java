package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

public class AtomSolutionIterator extends SolutionIterator {

    boolean read;
    Map<TRSVariable, TRSTerm> subs;

    private AtomSolutionIterator(Map<TRSVariable, TRSTerm> subs, Object id) {
        super(id);
        this.subs = subs;
        this.read = (this.subs == null);
    }

    /*
     * a ==> b * sigma
     */
    public static
        SolutionIterator
        create(Direction dir, TermAtom a, TermAtom b, SolutionConstraints solcons, Object id)
    {
        Map<TRSVariable, TRSTerm> subs = new LinkedHashMap<TRSVariable, TRSTerm>();
        subs = b.getLeft().extendMatchingSubstitution(subs, a.getLeft());
        subs = b.getRight().extendMatchingSubstitution(subs, a.getRight());
        if (subs == null) {
            return SolutionIterator.emptySolutionIterator;
        }
        for (TRSTerm t : subs.values()) {
            if (!solcons.checkReplacement(t)) {
                return SolutionIterator.emptySolutionIterator;
            }
        }
        return new AtomSolutionIterator(subs, id);
    }

    @Override
    public boolean next() {
        return true;
    }

    @Override
    public boolean isEmpty() {
        return this.subs == null;
    }

    @Override
    public boolean extendWithCurrent(Solution sol) {
        if (this.subs == null) {
            sol.setNotValid();
            return false;
        }
        if (!sol.isValid()) {
            return false;
        }
        return sol.checkIdBlocked(this.id) && sol.extendWith(this.subs);
    }

}
