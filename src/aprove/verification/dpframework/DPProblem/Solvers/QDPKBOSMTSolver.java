package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * @author thetux
 *
 */
public class QDPKBOSMTSolver implements QActiveSolver {

    private final SMTEngine engine;
    private boolean quasi  = false;
    private boolean status = false;

    public QDPKBOSMTSolver(final boolean quasi, final boolean status, final SMTEngine engine) {
        this.engine = engine;
        this.status = status;
        this.quasi  = quasi;
    }

    @Override
    public QActiveOrder solveQActive(final Set<? extends GeneralizedRule> P, final Map<? extends GeneralizedRule, QActiveCondition> R,
            final boolean active, final boolean allstrict, final Abortion aborter)
            throws AbortionException {

        final Set<GeneralizedRule> rules = new LinkedHashSet<GeneralizedRule>(R.keySet());

        final KBOSMTSolver solver = new KBOSMTSolver(this.quasi, this.status, this.engine);
        ExportableOrder<TRSTerm> solvingOrder;

        if (allstrict) {
            final Set<Constraint<TRSTerm>> cons = Constraint.fromRules(rules, OrderRelation.GE);
            cons.addAll(Constraint.fromRules(P, OrderRelation.GR));
            solvingOrder = solver.solve(cons, null, aborter);
        } else {
            solvingOrder = solver.solve(Constraint.fromRules(rules, OrderRelation.GE), P, aborter);
        }

        // To-Do: implement search for afs
        if (solvingOrder != null) {
            // create empty AFS over signature
            final Afs afs = new Afs();
            final Set<FunctionSymbol> fs = new HashSet<>();
            for (final GeneralizedRule rule : rules) {
                fs.addAll(rule.getFunctionSymbols());
            }
            for (final GeneralizedRule rule : P) {
                fs.addAll(rule.getFunctionSymbols());
            }
            for (final FunctionSymbol f : fs) {
                afs.setNoFiltering(f);
            }
            return new AfsOrder(afs, solvingOrder);
        }
        return null;
    }

}
