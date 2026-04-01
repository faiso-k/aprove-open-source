package aprove.verification.dpframework.TRSProblem.Solvers;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Wrapper class for RRR solving with POLO constraints and mu monotonicity.
 *
 * @author Andreas Kelle-Emden
 */
public class RRRMuPoloSolver implements RRRMuSolver {

    private POLOFactory factory;
    private boolean autostrict;
    private boolean autostrictJar;

    public RRRMuPoloSolver(POLOFactory factory, boolean autostrict, boolean autostrictJar) {
        this.factory = factory;
        this.autostrict = autostrict;
        this.autostrictJar = autostrictJar;
    }

    @Override
    public boolean isRRRMuApplicable(Set<Rule> R,
            ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu) {
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRRMu(Set<Rule> R,
            ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu,
            Abortion aborter) throws AbortionException {

        Set<Constraint<TRSTerm>> constraints;
        constraints = Constraint.fromRules(R, OrderRelation.GE);
        Set<VarPolyConstraint> polyConstraints;
        POLOSolver solver = (POLOSolver) this.factory.getSolver(constraints);
        solver.setAllowWeakMonotonicity(false);
        solver.setMu(mu);
        polyConstraints = solver.createPoloConstraints(aborter, constraints);

        POLO order;
        if (this.autostrict) {
            solver.addASC(polyConstraints, this.autostrictJar);
            order = solver.solve(aborter, polyConstraints);
        }
        else { // searchstrict
            order = solver.solve(aborter,
                    new HashSet<VarPolyConstraint>(0), polyConstraints);
        }
        return order;
    }

}
