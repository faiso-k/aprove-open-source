/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.Solvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Find a POLO using general polynomials over natural numbers.
 * @author cotto
 */
public class GPoloNatSolver
    extends AbstractPoloSolver<BigIntImmutable>
    implements QActiveSolver, RRRSolver, DirectSolver {
    /**
     * The strict mode used here.
     */
    private final StrictMode strictMode;

    /**
     * The form of the to-be-constructed polynomials.
     */
    private GInterpretationMode<BigIntImmutable> form;

    /**
     * This visitor generates flat representations of OrderPolys, where the
     * coefficients will not be flattened (depending on the factory used to
     * create the flattening visitor).
     */
    private FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outer;

    /**
     * This visitor generates flat representations of the inner polynomials,
     * which are coefficients of the outer polynomials.
     */
    private FlatteningVisitor<BigIntImmutable, GPolyVar> inner;

    /**
     * The default range for the variables.
     */
    private OPCRange<BigIntImmutable> range;

    /**
     * This factory will be used to create new order polynomials.
     */
    private OrderPolyFactory<BigIntImmutable> orderPolyFactory;

    /**
     * This factory can create the outer polynomials. It will be used in the
     * orderPolyFactory and interpretation.
     */
    private GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>
        bigPolyFactory;

    /**
     * This solver is able to take OPCs and provide some solution.
     */
    private OPCSolver<BigIntImmutable> solver;

    /**
     * This factory will be used to create new polynomials
     * (coefficients of order polynomials).
     */
    private GPolyFactory<BigIntImmutable, GPolyVar> polyFactory;

    /**
     * Create the solver based on the given parameters.
     * @param form The form of the polynomials as specified in the
     * strategy.
     * @param rangeParam The range of the variables.
     * @param monotoneParam Find a monotone ordering?
     * @param strictModeParam The strict mode that should be used. May be null,
     *          (and will be ignored) if the Solver is only used for RRR or
     *          Direct solving
     * @param opcSolver The solver that is able to transform and solve order
     * poly constraints.
     */
    public GPoloNatSolver(
            final GInterpretationMode<BigIntImmutable> form,
            final int rangeParam,
            final StrictMode strictModeParam,
            final OPCSolver<BigIntImmutable> opcSolver) {
        this.form = form;
        BigIntImmutable rangeBigInt =
            BigIntImmutable.create(BigInteger.valueOf(rangeParam));
        this.range = new OPCRange<BigIntImmutable>(rangeBigInt, rangeBigInt);
        this.strictMode = strictModeParam;
        Ring<BigIntImmutable> ringC = new BigIntImmutableRing();
        CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<GPolyVar>();
        this.polyFactory = new FullSharingFactory<BigIntImmutable, GPolyVar>();
        this.bigPolyFactory = new FullSharingFactory<
                GPoly<BigIntImmutable, GPolyVar>, GPolyVar>();
        this.orderPolyFactory = new OrderPolyFactory<BigIntImmutable>(
                    this.bigPolyFactory, this.polyFactory);

        GPolyFlatRing<BigIntImmutable, GPolyVar> flatRing =
            new SimpleGPolyFlatRing<BigIntImmutable, GPolyVar>(ringC, monoid);
        this.inner = new FlatteningVisitor<BigIntImmutable, GPolyVar>(flatRing);

        GPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> flatRing2 =
            new SimpleGPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>,
                GPolyVar>(this.polyFactory, monoid);
        this.outer =
            new FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(
                    flatRing2);

        opcSolver.setFvInner(this.inner);
        opcSolver.setFvOuter(this.outer);
        opcSolver.setPolyRing(this.polyFactory);
        this.solver = opcSolver;
    }

    /**
     * Try to solve the given problem defined by rule constraints.
     * @param pRules The pairs (P).
     * @param rules The rules with the corresponding QActiveCondition.
     * @param active not used.
     * @param allstrict this parameter is not used, use strategy parameter for
     * GPOLONAT!
     * @param aborter The aborter is used to abort calculations after some time.
     * @throws AbortionException Thrown when the aborter gets active.
     * @return A order solving the problem if it can be found.
     */
    @Override
    public QActiveOrder solveQActive(
            final Set<? extends GeneralizedRule> pRules,
            final Map<? extends GeneralizedRule, QActiveCondition> rules,
            final boolean active,
            final boolean allstrict,
            final Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert(this.strictMode != null);
        }
        return this.doSolve(pRules, rules, this.strictMode, false, aborter);
    }

    @Override
    public boolean isRRRApplicable(Set<Rule> R) {
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRR(Set<Rule> R, Abortion aborter)
            throws AbortionException {
        return this.doSolve(R, Collections.<Rule,QActiveCondition>emptyMap(),
                this.strictMode, true, aborter);
    }

    @Override
    public ExportableOrder<TRSTerm> solveDirect(Set<Rule> R, Abortion aborter)
            throws AbortionException {
        return this.doSolve(R,  Collections.<Rule,QActiveCondition>emptyMap(),
                StrictMode.ALLSTRICT, true, aborter);
    }

    private QActiveOrder doSolve(final Set<? extends GeneralizedRule> pRules,
            final Map<? extends GeneralizedRule, QActiveCondition> rules,
            final StrictMode strictMode,
            final boolean monotonic,
            final Abortion aborter)
            throws AbortionException {
        // step 1, generate constraints
        CoeffOrder<BigIntImmutable> coeffOrder = new BigIntImmutableOrder();
        ConstraintFactory<BigIntImmutable> constraintFactory =
            new SimpleFactory<BigIntImmutable>();
        GPolyFactory<BigIntImmutable, GPolyVar> coeffFactory =
            new FullSharingFactory<BigIntImmutable, GPolyVar>();
        OrderRelation rel;
        if (strictMode.equals(StrictMode.ALLSTRICT)) {
            rel = OrderRelation.GR;
        } else {
            // AUTOSTRICT, AUTOSTRICTJAR or SEARCHSTRICT
            rel = OrderRelation.GE;
        }
        List<Citation> citations = new ArrayList<Citation>(1);
        citations.add(Citation.POLO);
        Set<Constraint<TRSTerm>> pConstraints = Constraint.fromRules(pRules, rel);

        // create a new interpretation and interpret all function symbols
        // occurring in the pConstraints
        GInterpretation<BigIntImmutable> interpretation =
            GInterpretation.<BigIntImmutable>create(
                    pConstraints, this.form,
                    this.bigPolyFactory, coeffFactory, constraintFactory,
                    this.inner, this.outer, coeffOrder, citations, aborter);

        BigIntImmutable one = BigIntImmutable.create(BigInteger.ONE);
        OPCRange<BigIntImmutable> boolRange =
            new OPCRange<BigIntImmutable>(one, one);
        aborter.checkAbortion();
        Set<OrderPolyConstraint<BigIntImmutable>> constraintSet =
            this.generateWithStrictModeConstraints(pConstraints, strictMode,
                    interpretation, coeffFactory, this.orderPolyFactory,
                    constraintFactory, aborter);
        aborter.checkAbortion();
        OrderPolyConstraint<BigIntImmutable> usableRulesConstraint =
            interpretation.getActiveRuleConstraints(rules, this.form,
                    boolRange, aborter);
        constraintSet.add(usableRulesConstraint);

        if (monotonic) {
            Set<OrderPolyConstraint<BigIntImmutable>> monotonicityConstraint =
                interpretation.getStrongMonotonicityConstraints();
            constraintSet.addAll(monotonicityConstraint);
        }

        OrderPolyConstraint<BigIntImmutable> newConstraint =
            constraintFactory.createAnd(constraintSet);
        newConstraint =
            constraintFactory.createQuantifierE(
                    newConstraint, newConstraint.getFreeVariables());

        // step 2, feed the constraint to the solver and try to solve it
        Ring<BigIntImmutable> ring = (Ring<BigIntImmutable>)this.inner.getRingC();

        Map<GPolyVar, BigIntImmutable> solution =
            this.solver.solve(newConstraint, interpretation.getRanges(),
                    this.range, aborter);

        this.polyFactory.clear();

        if (solution == null) {
            return null;
        }

        // step 3, build some order out of the solution
        GInterpretation<BigIntImmutable> inter =
            interpretation.specialize(solution, ring.zero(), aborter);
        GPOLONAT solvingOrder =
            new GPOLONAT(inter, this.orderPolyFactory, this.inner, this.outer);
        return solvingOrder;
    }
}
