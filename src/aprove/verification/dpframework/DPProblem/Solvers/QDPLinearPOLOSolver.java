package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;

/**
 * @author Andreas Kelle-Emden
 */
public class QDPLinearPOLOSolver implements QActiveSolver {

    private SMTEngine engine;
    private AFSType afsType;
    private int numBits;

    public QDPLinearPOLOSolver(SMTEngine engine, AFSType afsType, int numBits) {
        this.engine = engine;
        this.afsType = afsType;
        this.numBits = numBits;
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean active, boolean allstrict, Abortion aborter)
            throws AbortionException {


        LinearPOLOSolver solver = new LinearPOLOSolver(this.engine, this.afsType, this.numBits);
        POLO solvingOrder;

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
