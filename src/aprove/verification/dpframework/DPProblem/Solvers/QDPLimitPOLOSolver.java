package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

/**
 * QDP Limit Polo order processor. Tries to orient P and all usable rules of P non-strictly
 * and at least one rule of P strictly, then deletes the strictly oriented
 * rules from P. Heavily derived from QDPPoloProccessor
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class QDPLimitPOLOSolver implements QActiveSolver {

    private LimitPOLOFactory factory;

    public QDPLimitPOLOSolver(LimitPOLOFactory factory) {
        this.factory = factory;
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R, boolean active, boolean allstrict, Abortion aborter) throws AbortionException {
        LimitPOLOSolver solver;

        Set<Constraint<TRSTerm>> pConstraints = Constraint.fromRules(P,OrderRelation.GE);
        Map<Constraint<TRSTerm>, QActiveCondition> rConstraints = new LinkedHashMap<Constraint<TRSTerm>, QActiveCondition>();
        for (Map.Entry<? extends GeneralizedRule, QActiveCondition>rule: R.entrySet()) {
            rConstraints.put(Constraint.fromRule(rule.getKey(), OrderRelation.GE), rule.getValue());
        }
        solver = this.factory.getSolver(Constraint.fromRules(R.keySet(), OrderRelation.GE), pConstraints, active);

        try {
            return solver.solve(rConstraints, pConstraints, aborter);
        } catch (BuiltTooManyException e) {
            return null;
        }
    }

}

