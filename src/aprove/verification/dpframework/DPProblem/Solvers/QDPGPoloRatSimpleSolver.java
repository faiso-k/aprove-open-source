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
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Find a POLO using general polynomials over rational numbers.
 * @author cotto
 * @version $Id$
 */
public class QDPGPoloRatSimpleSolver
    extends AbstractPoloSolver<MbyN>
    implements QActiveSolver {
    /**
     * The strict mode used here.
     */
    private final StrictMode strictMode;

    /**
     * The form of the to-be-constructed polynomials.
     */
    private GInterpretationMode<MbyN> form;

    /**
     * This visitor generates flat representations of OrderPolys, where the
     * coefficients will not be flattened (depending on the factory used to
     * create the flattening visitor).
     */
    private FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar> outer;

    /**
     * This visitor generates flat representations of the inner polynomials,
     * which are coefficients of the outer polynomials.
     */
    private FlatteningVisitor<MbyN, GPolyVar> inner;

    /**
     * The range used for the numerator.
     */
    private int numRange;

    /**
     * The range used for the denominator.
     */
    private int denomRange;

    /**
     * The domain used instead of ranges
     */
    private Domain domain;

    /**
     * This factory will be used to create new order polynomials.
     */
    private OrderPolyFactory<MbyN> orderPolyFactory;

    /**
     * This factory can create the outer polynomials. It will be used in the
     * orderPolyFactory and interpretation.
     */
    private GPolyFactory<GPoly<MbyN, GPolyVar>, GPolyVar>
        bigPolyFactory;

    /**
     * Decides where to allow non-natural coefficients.
     */
    private RatHeuristic heuristic;

    /**
     * This solver is able to take OPCs and provide some solution.
     */
    private OPCSolver<MbyN> solver;

    /**
     * This factory will be used to create new polynomials
     * (coefficients of order polynomials).
     */
    private GPolyFactory<MbyN, GPolyVar> polyFactory;

    /**
     * Create the solver based on the given parameters.
     * @param form The form of the polynomials as specified in the
     * strategy.
     * @param numeratorRange The range used for the numerator.
     * @param denominatorRange The range used for the denominator.
     * @param strictModeParam The strict mode that should be used.
     * @param opcSolver The solver that is able to transform and solve order
     * poly constraints.
     * @param ratHeur The heuristic to be used.
     */
    public QDPGPoloRatSimpleSolver(
            final GInterpretationMode<MbyN> form,
            final int numeratorRange,
            final int denominatorRange,
            final Domain domain,
            final StrictMode strictModeParam,
            final OPCSolver<MbyN> opcSolver,
            final RatHeuristic ratHeur) {
        this.form = form;
        this.numRange = numeratorRange;
        this.denomRange = denominatorRange;
        this.domain = domain;
        this.strictMode = strictModeParam;
        Ring<MbyN> ringC = new MbyNRing();
        CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<GPolyVar>();
        this.polyFactory = new FullSharingFactory<MbyN, GPolyVar>();
        this.bigPolyFactory = new FullSharingFactory<
                GPoly<MbyN, GPolyVar>, GPolyVar>();
        this.orderPolyFactory = new OrderPolyFactory<MbyN>(
                    this.bigPolyFactory, this.polyFactory);

        GPolyFlatRing<MbyN, GPolyVar> flatRing =
            new SimpleGPolyFlatRing<MbyN, GPolyVar>(ringC, monoid);
        this.inner = new FlatteningVisitor<MbyN, GPolyVar>(flatRing);

        GPolyFlatRing<GPoly<MbyN, GPolyVar>, GPolyVar> flatRing2 =
            new SimpleGPolyFlatRing<GPoly<MbyN, GPolyVar>,
                GPolyVar>(this.polyFactory, monoid);
        this.outer =
            new FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar>(
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
     * GPOLORATSIMPLE!
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
        CoeffOrder<MbyN> coeffOrder = new MbyNOrder();
        ConstraintFactory<MbyN> constraintFactory =
            new SimpleFactory<MbyN>();
        GPolyFactory<MbyN, GPolyVar> coeffFactory =
            new FullSharingFactory<MbyN, GPolyVar>();
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
        GInterpretation<MbyN> interpretation =
            GInterpretation.<MbyN>create(
                    pConstraints, this.form,
                    this.bigPolyFactory, coeffFactory, constraintFactory,
                    this.inner, this.outer, coeffOrder, citations, aborter);

        // The range should be interpreted as follows:
        // 1) Only one pair may exist
        // 2) The first element in this pair defines the range for the
        // numerator
        // 3) The second element in this pair defines the range for the
        // denominator (excluding 0).
        MbyN one = MbyN.ONE;
        OPCRange<MbyN> boolRange = new OPCRange<MbyN>(one, one);
        aborter.checkAbortion();
        OrderPolyConstraint<MbyN> usableRulesConstraint =
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
        OrderPolyConstraint<MbyN> newConstraint =
            this.generateConstraints(pConstraints, usableRulesConstraint,
                    strictModeToUse, interpretation, coeffFactory,
                    this.orderPolyFactory, constraintFactory,
                    aborter);
        // step 2, feed the constraint to the solver and try to solve it
        Ring<MbyN> ring = (Ring<MbyN>)this.inner.getRingC();

        MbyN numeratorRange = MbyN.create(BigInteger.valueOf(this.numRange));
        MbyN denominatorRange =
            MbyN.create(BigInteger.valueOf(this.denomRange));
        OPCRange<MbyN> defaultRange = new OPCRange<MbyN>(numeratorRange,
                                                         denominatorRange);

        // first use heuristics to determine where rational coeffs are
        // allowed and restrict the ranges if they are not
        this.heuristic.setPR(pRules, rules.keySet());

        Map<GPolyVar, OPCRange<MbyN>> ranges = interpretation.getRanges();
        //Map<FunctionSymbol, OrderPoly<MbyN>> pol = interpretation.getPol();

        OPCRange<MbyN> natRange;
        if (this.solver instanceof MbyNtoFormula
                && ((MbyNtoFormula) this.solver).getDenomFixed()
                && this.domain == null) {
            int maxValInt = this.numRange / this.denomRange;
            BigInteger maxVal = BigInteger.valueOf(maxValInt);
            MbyN maxValMN = MbyN.create(maxVal);
            natRange = new OPCRange<MbyN>(maxValMN, MbyN.ONE);
        } else {
            natRange = new OPCRange<MbyN>(numeratorRange, MbyN.ONE);
        }

        if (! this.heuristic.allowRat()) {
            return null;
            // defaultRange = natRange;
        }

        // FIXME variable-dependent ranges do not seem to be handled
        //       the way they should :-(

        /*
        for (Entry<FunctionSymbol, OrderPoly<MbyN>> fPol : pol.entrySet()) {
            FunctionSymbol f = fPol.getKey();
            OrderPoly<MbyN> poly = fPol.getValue();
            if (! this.heuristic.allowRat(f)) {
                ImmutableSet<GPolyVar> coeffs = poly.getInnerVariables();
                for (GPolyVar coeff : coeffs) {
                    ranges.put(coeff, natRange);
                }
            }
        }
        */

        // now go for it and solve depending on acting on ranges or a domain
        Map<GPolyVar, MbyN> solution;
        if (this.domain != null) {
            solution = this.solver.solve(newConstraint, this.domain, aborter);
        } else {
            solution = this.solver.solve(newConstraint, ranges, defaultRange,
                    aborter);
        }

        this.polyFactory.clear();
        coeffFactory.clear();

        if (solution == null) {
            return null;
        }

        // step 3, build some order out of the solution
        GInterpretation<MbyN> inter =
            interpretation.specialize(solution, ring.zero(), aborter);
        GPOLORATSIMPLE solvingOrder =
            new GPOLORATSIMPLE(inter, this.orderPolyFactory, this.inner,
                    this.outer, pRules);
        return solvingOrder;
    }
}
