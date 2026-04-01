package aprove.verification.dpframework.TRSProblem.Solvers;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;

public class AbortableDirectSolver implements DirectSolver {

    private SolverFactory factory;

    public AbortableDirectSolver(SolverFactory factory) {
        this.factory = factory;
    }

    @Override
    public ExportableOrder<TRSTerm> solveDirect(Set<Rule> R, Abortion aborter) throws AbortionException {
        Set<Constraint<TRSTerm>> cs = Constraint.fromRules(R, OrderRelation.GR);
        AbortableConstraintSolver<TRSTerm> solver = this.factory.getSolver(cs);
        ExportableOrder<TRSTerm> order = solver.solve(cs, aborter);
        return order;
    }

}
