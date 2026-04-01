package aprove.verification.oldframework.IRSwT.Engines;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.IRSwT.Orders.*;
import aprove.verification.oldframework.IRSwT.Processors.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Generates term order by calling an AbortableConstraintSolver.
 * @author Matthias Hoelzel
 */
public final class SolverBasedTermOrderEngine extends TermOrderEngine {
    /**
     * Store the strictly oriented (prepared) rules.
     * Computed by the method createConstraints().
     * */
    private final Set<IGeneralizedRule> strictPreparedRules;

    /**
     * Which term order are we trying to find?
     */
    private final OrderType orderType;

    /**
     * Constructor!
     * @param inputRules some rules to be analyzed
     * @param sorts sort dictionary
     * @param ot type of the order we are trying to find
     * @param abortion some aborter
     * @param freshNameGenerator some name generator
     */
    public SolverBasedTermOrderEngine(
        final Set<IGeneralizedRule> inputRules,
        final SortDictionary sorts,
        final OrderType ot,
        final Abortion abortion,
        final FreshNameGenerator freshNameGenerator)
    {
        super(inputRules, sorts, abortion, freshNameGenerator);
        this.strictPreparedRules = new LinkedHashSet<>();
        this.orderType = ot;
        assert this.orderType != OrderType.INTERPRETATION : "Wrong engine: Interpretation order is not a pure term order.";
    }

    @Override
    protected AbstractOrder generateTermOrder() throws AbortionException {
        final AbortableConstraintSolver<TRSTerm> acs = this.createSolver();
        final LinkedHashSet<Constraint<TRSTerm>> constraints = this.createConstraints();

        if (this.strictPreparedRules.isEmpty()) {
            return null;
        }

        final ExportableOrder<TRSTerm> eo = acs.solve(constraints, this.aborter);

        if (eo != null) {
            final LinkedHashSet<IGeneralizedRule> strictRules = new LinkedHashSet<>();
            for (final IGeneralizedRule prepRule : this.strictPreparedRules) {
                strictRules.addAll(this.filter.getOldRules(prepRule));
            }
            return new TermOrder(this.rules, strictRules, eo, this.filter);
        } else {
            return null;
        }
    }

    /**
     * Creates the constraints that are passed to the solver.
     * @return set of constraints to be solved
     */
    private LinkedHashSet<Constraint<TRSTerm>> createConstraints() {
        final LinkedHashSet<Constraint<TRSTerm>> constraints = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : this.preparedRules) {
            final TRSTerm left = rule.getLeft();
            final TRSTerm right = rule.getRight();
            if (left.unifies(right)) {
                constraints.add(Constraint.create(left, right, OrderRelation.GE));
            } else {
                constraints.add(Constraint.create(left, right, OrderRelation.GR));
                this.strictPreparedRules.add(rule);
            }
        }
        return constraints;
    }

    /**
     * Creates the right solver.
     * @return an abortable constraint solver
     */
    protected AbortableConstraintSolver<TRSTerm> createSolver() {
        switch (this.orderType) {
        case EMB_SOLVER:
            return EMBSolver.create();
        case LPOS_DEPTH_SOLVER:
            return LPOSDepthSolver.create(this.symbolsAfterPreparation.getSymbols());
        case LPO_DEPTH_SOLVER:
            return LPOSDepthSolver.create(this.symbolsAfterPreparation.getSymbols());
        case LPOS_BREADTH_SOLVER:
            return LPOSBreadthSolver.create(this.symbolsAfterPreparation.getSymbols());
        case LPO_BREADTH_SOLVER:
            return LPOBreadthSolver.create(this.symbolsAfterPreparation.getSymbols());
        case RPOS_DEPTH_SOLVER:
            return RPOSDepthSolver.create(this.symbolsAfterPreparation.getSymbols());
        case RPOS_BREADTH_SOLVER:
            return RPOSBreadthSolver.create(this.symbolsAfterPreparation.getSymbols());
        case RPO_DEPTH_SOLVER:
            return RPODepthSolver.create(this.symbolsAfterPreparation.getSymbols());
        case RPO_BREADTH_SOLVER:
            return RPOBreadthSolver.create(this.symbolsAfterPreparation.getSymbols());
        case KBO_SOLVER:
            return KBOSolver.create();
        case KBO_POLO_SMT_SOLVER:
            return new KBOPOLOSolver(new SMTLIBEngine());
        case KBO_POLO_SOLVER:
            return new KBOSMTSolver(true, true, new SMTLIBEngine());
        case ARCTIC_POLO:
            return new ArcticPOLOSolver(new SMTLIBEngine());
        case QLPOS_DEPTH_SOLVER:
            return QLPOSDepthSolver.create(this.symbolsAfterPreparation.getDefinedSymbols());
        case QLPOS_BREADTH_SOLVER:
            return QLPOSBreadthSolver.create(this.symbolsAfterPreparation.getDefinedSymbols());
        case QLPO_DEPTH_SOLVER:
            return QLPODepthSolver.create(this.symbolsAfterPreparation.getDefinedSymbols());
        case QLPO_BREADTH_SOLVER:
            return QLPOBreadthSolver.create(this.symbolsAfterPreparation.getDefinedSymbols());
        case QRPOS_DEPTH_SOLVER:
            return QRPOSDepthSolver.create(this.symbolsAfterPreparation.getDefinedSymbols());
        case QRPOS_BREADTH_SOLVER:
            return QRPOSBreadthSolver.create(this.symbolsAfterPreparation.getDefinedSymbols());
        case QRPO_DEPTH_SOLVER:
            return QRPODepthSolver.create(this.symbolsAfterPreparation.getDefinedSymbols());
        case QRPO_BREADTH_SOLVER:
            return QRPOBreadthSolver.create(this.symbolsAfterPreparation.getDefinedSymbols());
        case INTERPRETATION:
            assert false : "Wrong engine: Use interpretation engine for interpretations!";
        default:
            assert false : "Default?";
        }
        return null;
    }
}
