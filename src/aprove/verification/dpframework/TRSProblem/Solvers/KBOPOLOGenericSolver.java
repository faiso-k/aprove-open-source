package aprove.verification.dpframework.TRSProblem.Solvers;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * RRR solvers for KBOPOLO.
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class KBOPOLOGenericSolver implements DirectSolver, RRRSolver, RRRMuSolver,
        QActiveSolver {

    private SMTEngine engine;

    public KBOPOLOGenericSolver(SMTEngine engine) {
        this.engine = engine;
    }

    @Override
    public boolean isRRRApplicable(Set<Rule> R) {
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRR(Set<Rule> R, Abortion aborter)
    throws AbortionException {

        KBOPOLOSolver solver = new KBOPOLOSolver(this.engine);

        return solver.solve(null, R, aborter);
    }

    @Override
    public boolean isRRRMuApplicable(Set<Rule> R,  ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu) {
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRRMu(Set<Rule> R,  ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu, Abortion aborter)
    throws AbortionException {

        KBOPOLOSolver solver = new KBOPOLOSolver(this.engine);

        return solver.solve(null, R, aborter);
    }

    @Override
    public ExportableOrder<TRSTerm> solveDirect(Set<Rule> R, Abortion aborter)
    throws AbortionException {

        KBOPOLOSolver solver = new KBOPOLOSolver(this.engine);

        return solver.solve(Constraint.fromRules(R, OrderRelation.GR), null, aborter);
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean active, boolean allstrict, Abortion aborter)
            throws AbortionException {

        Set<GeneralizedRule> rules = new LinkedHashSet<GeneralizedRule>(R.keySet());

        KBOPOLOSolver solver = new KBOPOLOSolver(this.engine);
        POLO solvingOrder;

        if (allstrict) {
            Set<Constraint<TRSTerm>> cons = Constraint.fromRules(rules, OrderRelation.GE);
            cons.addAll(Constraint.fromRules(P, OrderRelation.GR));
            solvingOrder = solver.solve(cons, null, aborter);
        } else {
            solvingOrder = solver.solve(Constraint.fromRules(rules, OrderRelation.GE), P, aborter);
        }

        return solvingOrder;
    }


}
