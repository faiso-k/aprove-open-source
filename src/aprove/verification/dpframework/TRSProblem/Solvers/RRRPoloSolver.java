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

/**
 * Wrapper class for RRR solving with POLO constraints
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class RRRPoloSolver implements RRRSolver {

    private POLOFactory factory;
    private boolean autostrict;
    private boolean autostrictJar;

    public RRRPoloSolver(POLOFactory factory, boolean autostrict, boolean autostrictJar) {
        this.factory = factory;
        this.autostrict = autostrict;
        this.autostrictJar = autostrictJar;
    }

    @Override
    public boolean isRRRApplicable(Set<Rule> R) {
        return true;
    }

    @Override
    public POLO solveRRR(Set<Rule> R, Abortion aborter)
            throws AbortionException {

        Set<Constraint<TRSTerm>> constraints;
        constraints = Constraint.fromRules(R, OrderRelation.GE);
        Set<VarPolyConstraint> polyConstraints;
        POLOSolver solver = (POLOSolver) this.factory.getSolver(constraints);
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
