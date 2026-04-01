/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.Solvers;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Find a POLO using general polynomials over rational numbers.
 * @author cotto
 * @version $Id$
 */
public class QDPGPoloRatSolver extends AbstractPoloSolver<PoT>
        implements QActiveSolver {
    /**
     * The strict mode used here.
     */
    private final StrictMode strictMode;

    /**
     * The form of the to-be-constructed polynomials.
     */
    private GInterpretationMode<PoT> form;

    /**
     * This visitor generates flat representations of OrderPolys, where the
     * coefficients will not be flattened (depending on the factory used to
     * create the flattening visitor).
     */
    private FlatteningVisitor<GPoly<PoT, GPolyVar>, GPolyVar> outer;

    /**
     * This visitor generates flat representations of the inner polynomials,
     * which are coefficients of the outer polynomials.
     */
    private FlatteningVisitor<PoT, GPolyVar> inner;

    /**
     * The smallest exponent that may be chosen for the variables.
     */
    private int expMin;

    /**
     * The greatest exponent that may be chosen for the variables.
     */
    private int expMax;

    /**
     * This factory will be used to create new order polynomials.
     */
    private OrderPolyFactory<PoT> orderPolyFactory;

    /**
     * This factory can create the outer polynomials. It will be used in the
     * orderPolyFactory and interpretation.
     */
    private GPolyFactory<GPoly<PoT, GPolyVar>, GPolyVar>
        bigPolyFactory;

    /**
     * Decides where to allow non-natural coefficients.
     */
    private RatHeuristic heuristic;

    /**
     * This solver is able to take OPCs and provide some solution.
     */
    private OPCSolver<PoT> solver;

    /**
     * This factory will be used to create new polynomials
     * (coefficients of order polynomials).
     */
    private GPolyFactory<PoT, GPolyVar> polyFactory;

    /**
     * Create the solver based on the given parameters.
     * @param form The form of the polynomials as specified in the
     * strategy.
     * @param min The smallest exponent that may be chosen for the variables.
     * @param max The greatest exponent that may be chosen for the variables.
     * @param strictModeParam The strict mode that should be used.
     * @param opcSolver The solver that is able to transform and solve order
     * poly constraints.
     */
    public QDPGPoloRatSolver(
            final GInterpretationMode<PoT> form,
            final int min,
            final int max,
            final StrictMode strictModeParam,
            final OPCSolver<PoT> opcSolver,
            final RatHeuristic ratHeur) {
        this.form = form;
        this.expMin = min;
        this.expMax = max;
        this.strictMode = strictModeParam;
        Ring<PoT> ringC = new PoTRing();
        CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<GPolyVar>();
        this.polyFactory = new FullSharingFactory<PoT, GPolyVar>();
        this.bigPolyFactory = new FullSharingFactory<
                GPoly<PoT, GPolyVar>, GPolyVar>();
        this.orderPolyFactory = new OrderPolyFactory<PoT>(
                    this.bigPolyFactory, this.polyFactory);

        GPolyFlatRing<PoT, GPolyVar> flatRing =
            new SimpleGPolyFlatRing<PoT, GPolyVar>(ringC, monoid);
        this.inner = new FlatteningVisitor<PoT, GPolyVar>(flatRing);

        GPolyFlatRing<GPoly<PoT, GPolyVar>, GPolyVar> flatRing2 =
            new SimpleGPolyFlatRing<GPoly<PoT, GPolyVar>,
                GPolyVar>(this.polyFactory, monoid);
        this.outer =
            new FlatteningVisitor<GPoly<PoT, GPolyVar>, GPolyVar>(
                    flatRing2);

        opcSolver.setFvInner(this.inner);
        opcSolver.setFvOuter(this.outer);
        opcSolver.setPolyRing(this.polyFactory);
        this.solver = opcSolver;
        this.heuristic = ratHeur;
    }

    /**
     * Try to solve the given problem defined by rule constraints.
     * @param pRules The pairs (P).
     * @param rules The rules with the corresponding QActiveCondition.
     * @param active not used.
     * @param allstrict this parameter is not used, use strategy parameter for
     * GPOLORAT!
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
        // step 1, generate constraints
        CoeffOrder<PoT> coeffOrder = new PoTOrder();
        ConstraintFactory<PoT> constraintFactory =
            new SimpleFactory<PoT>();
        GPolyFactory<PoT, GPolyVar> coeffFactory =
            new FullSharingFactory<PoT, GPolyVar>();
        OrderRelation rel;
        if (allstrict) {
            rel = OrderRelation.GR;
        } else {
            // AUTOSTRICT or AUTOSTRICTJAR
            rel = OrderRelation.GE;
        }
        List<Citation> citations = new ArrayList<Citation>(2);
        citations.add(Citation.POLO);
        citations.add(Citation.RATPOLO);
        Set<Constraint<TRSTerm>> pConstraints =
            Constraint.fromRulesinStandardRepresentation(pRules, rel);

        // create a new interpretation and interpret all function symbols
        // occurring in the pConstraints
        GInterpretation<PoT> interpretation =
            GInterpretation.<PoT>create(
                    pConstraints, this.form,
                    this.bigPolyFactory, coeffFactory, constraintFactory,
                    this.inner, this.outer, coeffOrder, citations, aborter);

        // The range should be interpreted as follows:
        // 0 = [0,0] is always allowed
        // The given range must be a list of size 1, where the single element
        // ([a, b], [c, d]) defines the range of the exponents.
        // This is b and d in this example. So the allowed values are
        // 0 and 2^b..2^d.
        // The range ([1, -1], [1, 1]) gives 0, 1/2, 1, 2 as possible values.
        PoT one = PoT.ONE;
        OPCRange<PoT> boolRange = new OPCRange<PoT>(one, one);
        aborter.checkAbortion();
        OrderPolyConstraint<PoT> usableRulesConstraint =
            interpretation.getActiveRuleConstraints(rules, this.form,
                    boolRange, aborter);

        // make sure that the allstrict parameter specified by the
        // caller is respected
        StrictMode strictModeToUse;
        if (allstrict) {
            strictModeToUse = StrictMode.ALLSTRICT;
        }
        else if (this.strictMode == StrictMode.ALLSTRICT) {
            strictModeToUse = StrictMode.SEARCHSTRICT;
        }
        else {
            strictModeToUse = this.strictMode;
        }
        aborter.checkAbortion();
        OrderPolyConstraint<PoT> newConstraint =
            this.generateConstraints(pConstraints, usableRulesConstraint,
                    strictModeToUse, interpretation, coeffFactory,
                    this.orderPolyFactory, constraintFactory, aborter);

        // step 2, feed the constraint to the solver and try to solve it
        Ring<PoT> ring = (Ring<PoT>)this.inner.getRingC();

        BigInteger oneBigInt = BigInteger.ONE;
        OPCRange<PoT> defaultRange =
            new OPCRange<PoT>(
                    PoT.create(oneBigInt, BigInteger.valueOf(this.expMin)),
                    PoT.create(oneBigInt, BigInteger.valueOf(this.expMax)));


        // first use heuristics to determine where rational coeffs are
        // allowed and restrict the ranges if they are not
        this.heuristic.setPR(pRules, rules.keySet());

        Map<GPolyVar, OPCRange<PoT>> ranges = interpretation.getRanges();
        //Map<FunctionSymbol, OrderPoly<PoT>> pol = interpretation.getPol();

        OPCRange<PoT> natRange;
        natRange = new OPCRange<PoT>(PoT.ZERO,
                PoT.create(oneBigInt, BigInteger.valueOf(this.expMax)));

        if (! this.heuristic.allowRat()) {
            defaultRange = natRange;
        }

        // FIXME variable-dependent ranges do not seem to be handled
        //       the way they should :-(

        /*
        for (Entry<FunctionSymbol, OrderPoly<PoT>> fPol : pol.entrySet()) {
            FunctionSymbol f = fPol.getKey();
            OrderPoly<PoT> poly = fPol.getValue();
            if (! this.heuristic.allowRat(f)) {
                ImmutableSet<GPolyVar> coeffs = poly.getInnerVariables();
                for (Variable coeff : coeffs) {
                    ranges.put(coeff, natRange);
                }
            }
        }
        */

        // now go for it and solve
        Map<GPolyVar, PoT> solution =
            this.solver.solve(newConstraint, ranges, defaultRange, aborter);

        this.polyFactory.clear();
        coeffFactory.clear();

        if (solution == null) {
            return null;
        }

        // step 3, build some order out of the solution
        GInterpretation<PoT> inter =
            interpretation.specialize(solution, ring.zero(), aborter);
        GPOLORAT solvingOrder =
            new GPOLORAT(inter, this.orderPolyFactory, this.inner, this.outer,
                    pRules);
        return solvingOrder;
    }
}
