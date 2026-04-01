package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;

/**
 * @author Andreas Kelle-Emden
 */
public class QDPArcticPOLOSolver implements QActiveSolver {

    private SMTEngine engine;

    public QDPArcticPOLOSolver(SMTEngine engine) {
        this.engine = engine;
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean active, boolean allstrict, Abortion aborter)
            throws AbortionException {


        ArcticPOLOSolver solver = new ArcticPOLOSolver(this.engine);
        ArcticPOLO solvingOrder;

        if (allstrict) {
            Set<GeneralizedRule> rules = new LinkedHashSet<GeneralizedRule>(R.keySet());
            Set<Constraint<TRSTerm>> cons = Constraint.fromRules(rules, OrderRelation.GE);
            cons.addAll(Constraint.fromRules(P, OrderRelation.GR));
            solvingOrder = solver.solve(cons, null, aborter);
        } else {
            solvingOrder = solver.solve(R, null, P, null, aborter);
        }

        return solvingOrder;
    }

}
