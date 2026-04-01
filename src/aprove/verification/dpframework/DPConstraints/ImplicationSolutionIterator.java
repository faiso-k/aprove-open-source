package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

public class ImplicationSolutionIterator extends SolutionIterator {

    SolutionIterator soli;
    SolutionIterator condsoli;
    ConstraintSet as;
    ConstraintSet bs;
    Set<TRSVariable> qa;
    Set<TRSVariable> qb;
    SolutionConstraints solcons;
    Direction dir;

    private ImplicationSolutionIterator(
        Direction dir,
        Set<TRSVariable> qa,
        Set<TRSVariable> qb,
        SolutionIterator soli,
        ConstraintSet as,
        ConstraintSet bs,
        SolutionConstraints solcons,
        Object id)
    {
        super(id);
        this.soli = soli;
        this.as = as;
        this.bs = bs;
        this.qa = qa;
        this.qb = qb;
        this.solcons = solcons;
        this.dir = dir;
    }

    public static SolutionIterator create(
        Direction dir,
        Implication a,
        Implication b,
        SolutionConstraints solcons,
        Object id)
    {
        SolutionIterator soli = SolutionIterator.create(dir, a.getConclusion(), b.getConclusion(), solcons, null);
        if (!soli.isEmpty()) {
            return new ImplicationSolutionIterator(
                dir,
                a.getQuantor(),
                b.getQuantor(),
                soli,
                a.getConditions(),
                b.getConditions(),
                solcons,
                id);
        }
        return SolutionIterator.emptySolutionIterator;
    }

    @Override
    public boolean isEmpty() {
        return this.soli == null;
    }

    @Override
    public boolean next() {
        return (this.soli == null) || (this.soli.next() && this.getCondsoli().next());
    }

    private SolutionIterator getCondsoli() {
        return (this.condsoli == null) ? this.condsoli =
            SetSolutionIterator.create(this.dir.inverse(), this.as, this.bs, this.solcons, null) : this.condsoli;
    }

    @Override
    public boolean extendWithCurrent(Solution sol) {
        if (!sol.isValid()) {
            return false;
        }
        if (this.soli == null) {
            sol.setNotValid();
            this.soli = null;
            return false;
        }
        if (this.soli.isEmpty()) {
            sol.setNotValid();
            return true;
        }
        if (this.getCondsoli().isEmpty()) {
            sol.setNotValid();
            this.soli = null;
            return true;
        }
        sol.addQuantors(this.qa, this.qb);
        boolean res = sol.checkIdBlocked(this.id);
        if (res) {
            sol.pushIdSet(null);
            res = res && this.soli.extendWithCurrent(sol) && this.condsoli.extendWithCurrent(sol);
            sol.popIdSet();
        }
        sol.popQuantors();
        return res;
    }

}
