package aprove.verification.dpframework.DPConstraints;

import java.util.*;

public class ASBListSolutionIterator extends InRowSolutionIterator {

    List<Constraint> as;
    Constraint b;
    SolutionConstraints solcons;
    Direction dir;
    List<? extends Object> ids;

    public ASBListSolutionIterator(
        Direction dir,
        List<Constraint> as,
        Constraint b,
        List<? extends Object> ids,
        SolutionConstraints solcons)
    {
        super(as.size());
        this.as = as;
        this.b = b;
        this.solcons = solcons;
        this.dir = dir;
        this.ids = ids;
    }

    @Override
    public SolutionIterator getSolutionIteratorFor(int pos) {
        return SolutionIterator.create(this.dir, this.as.get(pos), this.b, this.solcons, this.ids.get(pos));
    }

}
