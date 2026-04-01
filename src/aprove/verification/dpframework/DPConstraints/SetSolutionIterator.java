package aprove.verification.dpframework.DPConstraints;

import java.util.*;

public class SetSolutionIterator extends SolutionIterator {
    List<SolutionIterator> solis;
    Set<Object> idSet;

    public SetSolutionIterator(List<SolutionIterator> solis, Set<Object> idSet, Object id) {
        super(id);
        this.solis = solis;
        this.idSet = idSet;
    }

    public static SolutionIterator create(
        Direction dir,
        ConstraintSet as,
        ConstraintSet bs,
        SolutionConstraints solcons,
        Object id)
    {
        if (SolutionIterator.isCandidateSS(dir, as, bs)) {
            if (dir == Direction.right) {
                List<SolutionIterator> solis = new ArrayList<SolutionIterator>(bs.size());
                for (Constraint b : bs) {
                    List<Constraint> candidates = new ArrayList<Constraint>(as.size());
                    for (Constraint a : as) {
                        if (SolutionIterator.isCandidateCC(dir, a, b)) {
                            candidates.add(a);
                        }
                    }
                    if (candidates.isEmpty()) {
                        return SolutionIterator.emptySolutionIterator;
                    }
                    SolutionIterator soli;
                    if (candidates.size() == 1) {
                        soli = SolutionIterator.create(dir, candidates.get(0), b, solcons, candidates.get(0));
                    } else {
                        soli = new ASBListSolutionIterator(dir, candidates, b, candidates, solcons);
                    }
                    if (soli.isEmpty()) {
                        return SolutionIterator.emptySolutionIterator;
                    }
                    solis.add(soli);
                }
                return new SetSolutionIterator(solis, solcons.multiSet ? new LinkedHashSet<Object>() : null, id);
            } else {
                List<SolutionIterator> solis = new ArrayList<SolutionIterator>(as.size());
                for (Constraint a : as) {
                    List<Constraint> candidates = new ArrayList<Constraint>(bs.size());
                    for (Constraint b : bs) {
                        if (SolutionIterator.isCandidateCC(dir, a, b)) {
                            candidates.add(b);
                        }
                    }
                    if (candidates.isEmpty()) {
                        return SolutionIterator.emptySolutionIterator;
                    }
                    SolutionIterator soli;
                    if (candidates.size() == 1) {
                        soli = SolutionIterator.create(dir, a, candidates.get(0), solcons, candidates.get(0));
                    } else {
                        soli = new ABSListSolutionIterator(dir, a, candidates, candidates, solcons);
                    }
                    if (soli.isEmpty()) {
                        return SolutionIterator.emptySolutionIterator;
                    }
                    solis.add(soli);
                }
                return new SetSolutionIterator(solis, solcons.multiSet ? new LinkedHashSet<Object>() : null, id);
            }
        }
        return SolutionIterator.emptySolutionIterator;
    }

    @Override
    public boolean isEmpty() {
        return this.solis == null;
    }

    @Override
    public boolean next() {
        for (SolutionIterator soli : this.solis) {
            if (soli.isEmpty()) {
                this.solis = null;
                return true;
            }
            if (!soli.next()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean extendWithCurrent(Solution sol) {
        if (this.solis != null && sol.isValid()) {
            if (this.idSet != null) {
                this.idSet.clear();
            }
            sol.pushIdSet(this.idSet);
            for (SolutionIterator soli : this.solis) {
                if (soli.isEmpty()) {
                    sol.setNotValid();
                    this.solis = null;
                    sol.popIdSet();
                    return false;
                }
                if (!soli.extendWithCurrent(sol)) {
                    sol.popIdSet();
                    return false;
                }
            }
            sol.popIdSet();
            return sol.checkIdBlocked(this.id);
        }
        sol.setNotValid();
        return false;
    }

}
