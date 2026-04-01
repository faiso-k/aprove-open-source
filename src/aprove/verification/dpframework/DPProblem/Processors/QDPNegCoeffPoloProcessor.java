package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPReductionPairProcessor.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.Logic.*;
import immutables.*;

/**
 * Works like QDPReductionPairProcessor, but here we require that the lhs and
 * the rhs of the usable rules are equivalent instead of allowing the lhs to
 * be greater than the rhs. Consequently, the resulting order is not
 * CE-compatible.
 *
 * In other words, we regard a reduction triple (=, >=, >).
 *
 * Here, we use a polynomial order over the naturals with negative
 * constants *and negative coefficients of variables* to compare terms.
 *
 * @author Carsten Fuhs
 * @see QDPReductionPairProcessor
 */
public class QDPNegCoeffPoloProcessor extends QDPProblemProcessor {

    private final NEGCOEFFPOLOFactory factory;
    private final boolean usable;
    private final boolean active;
    private final boolean allstrict;
    private final boolean mergeMutual;

    @ParamsViaArgumentObject
    public QDPNegCoeffPoloProcessor(final Arguments arguments) {
        this.active = arguments.active;
        this.allstrict = arguments.allstrict;
        this.mergeMutual = arguments.mergeMutual;
        this.usable = arguments.usable;

        final NEGCOEFFPOLOFactory.Arguments facArgs =
            new NEGCOEFFPOLOFactory.Arguments();
        facArgs.engine = arguments.engine;
        facArgs.heuristic = arguments.heuristic;
        facArgs.negRange = arguments.negRange;
        facArgs.posRange = arguments.posRange;
        facArgs.satConverter = arguments.satConverter;
        facArgs.simplification = arguments.simplification;
        facArgs.stripExponents = arguments.stripExponents;
        this.factory = new NEGCOEFFPOLOFactory(facArgs);
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return true;
    }

    @Override
    protected Result processQDPProblem(final QDPProblem origqdp, final Abortion aborter) throws AbortionException {
        final QActiveSolver solver = this.factory.getQActiveSolver();
        // is it allowed to restrict to usable rules?
        final boolean useUsable = this.usable &&
                (origqdp.getInnermost() /*|| (origqdp.getMinimal() && this.factory.solversGenerateCECompatibleOrders())*/);
        final boolean useActive = this.active && useUsable;

        final Set<Rule> usableRules = useUsable ? origqdp.getUsableRules() : origqdp.getR();
        final Set<Rule> P = origqdp.getP();

        boolean allstrict = this.allstrict;
        if (!allstrict && P.size() == 1) {
            allstrict = true;
        }

        Map<Rule, QActiveCondition> active;
        if (useActive) {
            final QUsableRules used = origqdp.getQUsableRulesCalculator();
            active = used.getActiveConditions(P, this.mergeMutual);
        } else {
            active = QUsableRules.getRulesAsConditionMap(usableRules);
        }

        aborter.checkAbortion();
        final QActiveOrder solvingOrder = solver.solveQActive(P, active, useActive, allstrict, aborter);
        if (solvingOrder != null) {
            return QDPNegCoeffPoloProcessor.getResult(solvingOrder, active, origqdp);
        }
        return ResultFactory.unsuccessful();
    }

    /**
     * Standard method to compute the result of this processor.
     */
    public static Result getResult(
            final QActiveOrder order,
            final Map<Rule, QActiveCondition> active,
            final QDPProblem origqdp) throws AbortionException {

        // which rules are actually usable wrt the implicit argument filtering?
        final Set<Rule> usableRules = new LinkedHashSet<Rule>(active.size());
        for (final Map.Entry<Rule, QActiveCondition> entry : active.entrySet()) {
            if (order.checkQActiveCondition(entry.getValue())) {
                usableRules.add(entry.getKey());
            }
        }

        // check which elements of P have been oriented strictly
        Set<Rule> newPRules, deletedPRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();
        for (final Rule rule : origqdp.getP()) {
            // only add non-strictly oriented rules
            if (!order.solves(Constraint.fromRule(rule, OrderRelation.GR))) {
                newPRules.add(rule);
            } else {
                deletedPRules.add(rule);
            }
        }

        if (Globals.useAssertions) {
            for (final Rule rule : usableRules) {
                assert (order.solves(Constraint.fromRule(rule, OrderRelation.EQ)));
            }
            for (final Rule rule : origqdp.getP()) {
                assert (order.solves(Constraint.fromRule(rule, OrderRelation.GE)));
            }
            assert(! deletedPRules.isEmpty());
            for (final Rule rule : deletedPRules) {
                assert (order.solves(Constraint.fromRule(rule, OrderRelation.GR)));
            }
        }

        // build smaller subproblem and proof
        final QDPProblem newQdp = origqdp.getSubProblem(ImmutableCreator.create(newPRules));
        final Proof proof = new QDPOrderProof(deletedPRules, newPRules, order,
                usableRules, null, origqdp, newQdp);
        return ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);
    }

    public static class Arguments {
        public boolean active = true;
        public boolean allstrict = false;
        public Engine engine;
        public NegOpPOLOFactory.Heuristic heuristic;
        public boolean mergeMutual = false;
        public int negRange;
        public int posRange;
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean stripExponents;
        public boolean usable = true;
    }
}
