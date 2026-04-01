package aprove.verification.dpframework.DPConstraints;

import java.util.*;

public class ABSListSolutionIterator extends InRowSolutionIterator {

    Constraint a;
    List<Constraint> bs;
    List<? extends Object> ids;
    SolutionConstraints solcons;
    Direction dir;

    public ABSListSolutionIterator(
        Direction dir,
        Constraint a,
        List<Constraint> bs,
        List<? extends Object> ids,
        SolutionConstraints solcons)
    {
        super(bs.size());
        this.bs = bs;
        this.a = a;
        this.solcons = solcons;
        this.dir = dir;
        this.ids = ids;
    }

    @Override
    public SolutionIterator getSolutionIteratorFor(int pos) {
        return SolutionIterator.create(this.dir, this.a, this.bs.get(pos), this.solcons, this.ids.get(pos));
    }

}
