package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.PMATRO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.ArcticInt.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.PolyMatrices.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * A solver for exotic matrix interpretations.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PMatroExoticSolver<T extends ExoticInt<T>> implements QActiveSolver {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Solvers.PMatroExoticSolver");

    /**
     * A factory to obtain a SAT solver that is used to find an interpretation.
     */
    protected final Engine engine;

    /**
     * The dimension of the matrices to use.
     */
    protected final int dimension;

    /**
     * The highest allowed coefficient value.
     */
    protected final T maxValue;

    /**
     * The minimum value of coefficients to look for.
     * If this is negative, use Below Zero methods,
     * otherwise restrict yourself to naturals.
     */
    protected final T minValue;

    /**
     * The (semi-)ring the coefficients belong to.
     */
    protected final Semiring<T> ringC;

    /**
     * An order for the coefficients.
     */
    protected final CoeffOrder<T> coeffOrder;

    /**
     * A binarizer to obtain binary representations of coefficients.
     */
    protected final Binarizer<T> binarizer;

    /**
     * A factory for PolyCircuits representing the SAT encoding of constraints.
     */
    protected final CircuitFactory circuitFactory;

    /**
     * Use collapsing interpretations for applications of DP root symbols
     * (i.e., to numbers, not to vectors of numbers) if applicable?
     */
    protected final boolean collapse;

    /**
     * Some information about the specific interpretation used.
     */
    protected final String description;

    /**
     * Citations referring to the specific interpretation used.
     */
    protected final List<Citation> citations;

    /**
     * Whether to search for an extended monotone algebra (with > and >= being
     * monotone) or a weakly monotone one (with only >= being monotone).
     * Extended monotone algebras are used for RRR/MRR.
     */
    protected boolean extendedMonotone = false;

    /**
     * If we are using below-zero interpretations:
     * - True: Use "absolute positiveness" as descriped by
     *   Koprowski and Waldmann in their RTA'08 paper,
     *   i.e., the constant "addend" must be positive.
     * - False: Require "somewhere positiveness" as described by
     *   Sternagel and Thiemann in their RTA'14 paper,
     *   i.e., the constant addend or some coefficient matrix
     *   must be positive.
     */
    protected boolean absPos;

    /**
     * A factory for the actual type of exotic numbers
     * that we're working with.
     */
    private final ExoticIntFactory<T> intFactory;

    public PMatroExoticSolver(
            final Engine engine,
            final int dimension,
            final T minValue,
            final T maxValue,
            final Semiring<T> ringC,
            final CoeffOrder<T> coeffOrder,
            final ExoticIntFactory<T> intFactory,
            final ExoticIntBinarizer<T> binarizer,
            final CircuitFactory circuitFactory,
            final boolean collapse,
            final String description,
            final List<Citation> citations,
            final boolean absPos) {
        this.engine = engine;
        this.dimension = dimension;
        this.maxValue = maxValue;
        this.minValue = minValue;
        this.ringC = ringC;
        this.coeffOrder = coeffOrder;
        this.intFactory = intFactory;
        this.binarizer = binarizer;
        this.circuitFactory = circuitFactory;
        this.collapse = collapse;
        this.description = description;
        this.citations = citations;
        this.absPos = absPos;
    }

    /**
     * Create and solve (if possible) an arctic matrix interpretation for P and R.
     */
    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean active, boolean allstrict, Abortion aborter)
            throws AbortionException {

        // Arctic orders can be extended monotone only on string rewriting
        if (this.extendedMonotone) {
            for (GeneralizedRule rule : R.keySet()) {
                for (FunctionSymbol fsym : rule.getFunctionSymbols()) {
                    if (fsym.getArity() > 1) {
                        return null;
                    }
                }
            }
            for (GeneralizedRule rule : P) {
                for (FunctionSymbol fsym : rule.getFunctionSymbols()) {
                    if (fsym.getArity() > 1) {
                        return null;
                    }
                }
            }
        }

        // compute symbols for which collapsing interpretations
        // will be used
        Set<FunctionSymbol> collapsingSyms = null;
        if (this.collapse) {
            collapsingSyms =
                aprove.verification.dpframework.BasicStructures.CollectionUtils.getTupleSymbols(P, R.keySet());
        }
        if (collapsingSyms == null) {
            collapsingSyms = java.util.Collections.emptySet();
        }

        // create all necessary factories and such
        ConstraintFactory<T> constraintFactory =
            new SimpleFactory<T>();

        // Factories for the polynomials that go inside the matrices.
        FullSharingFactory<T, GPolyVar> matrixPolyFactory =
            new FullSharingFactory<T, GPolyVar>();
        FullSharingFactory<GPoly<T, GPolyVar>, GPolyVar>matrixBigPolyFactory =
            new FullSharingFactory<GPoly<T, GPolyVar>, GPolyVar>();
        OrderPolyFactory<T> matrixOrderPolyFactory =
            new OrderPolyFactory<T>(matrixBigPolyFactory, matrixPolyFactory);

        PolyMatrixFactory<T> matrixFactory =
            new PolyMatrixFactory<T>(matrixOrderPolyFactory, this.dimension);

        CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<GPolyVar>();
        GPolyFlatRing<GPoly<T, GPolyVar>, GPolyVar> outerFlatRing =
            new SimpleGPolyFlatRing<GPoly<T, GPolyVar>, GPolyVar>(
                    matrixPolyFactory, monoid);
        FlatteningVisitor<GPoly<T, GPolyVar>, GPolyVar> fv =
            new FlatteningVisitor<GPoly<T, GPolyVar>, GPolyVar>(outerFlatRing);

        // We need this a few times, so I'll just cast it once here.
        ExoticIntBinarizer<T> binarizer =
            (ExoticIntBinarizer<T>)this.binarizer;

        OrderRelation rel = OrderRelation.GR;
        Set<Constraint<TRSTerm>> pConstraints = Constraint.fromRules(P, rel);
        aborter.checkAbortion();

        // create a new interpretation and interpret all function symbols
        // occurring in the pConstraints
        long nanos1, nanos2;
        nanos1 = System.nanoTime();

        ExoticPolyMatrixInterpretation<T> interpretation =
            ExoticPolyMatrixInterpretation.<T>create(
                    pConstraints, this.ringC, fv, matrixOrderPolyFactory,
                    matrixFactory, constraintFactory, this.intFactory, this.minValue,
                    this.dimension, allstrict, collapsingSyms, this.description, this.citations);

        // generate constraints
        OrderPolyConstraint<T> usableRulesConstraint =
            interpretation.getActiveRuleConstraints(R, aborter);
        OrderPolyConstraint<T> newConstraint =
            interpretation.fromTermConstraints(pConstraints, aborter);
        if (Globals.DEBUG_ULRICHSG) {
            PMatroExoticSolver.log.setLevel(Level.FINE);
            System.out.println(interpretation);
            System.out.println("DP constraint is " + newConstraint);
            System.out.println("UsableRuleConstraint is " + usableRulesConstraint);
        }
        newConstraint = constraintFactory.createAnd(newConstraint, usableRulesConstraint);

        if (this.extendedMonotone) {
            newConstraint = constraintFactory.createAnd(newConstraint,
                    interpretation.getExtendedMonotonicityConstraint());
        }

        nanos2 = System.nanoTime();
        if (PMatroExoticSolver.log.isLoggable(Level.FINE)) {
            PMatroExoticSolver.log.fine("Building Exotic Matrix Constraints took "
                    + (nanos2-nanos1)/1000000 + " ms.\n");
        }

        if (this.minValue.signum() < 0) {
            binarizer.setShift(this.minValue.abs().intValue());
        }
        aborter.checkAbortion();

        // transform the constraint into a propositional formula

        nanos1 = System.nanoTime();

        FormulaFactory<None> formulaFactory = binarizer.getFormulaFactory();
        PolyToCircuitConverter<T, GPolyVar> polyToCircuit =
            new PolyToCircuitConverter<T, GPolyVar>(
                    this.circuitFactory, binarizer, this.maxValue);
        OPCtoFormulaConverter<T> opcToFormula =
            new OPCtoFormulaConverter<T>(polyToCircuit, formulaFactory);
        aborter.checkAbortion();

        if (Globals.DEBUG_FUHS) {
            GPolyFlatRing<T, GPolyVar> flatRing =
                new SimpleGPolyFlatRing<T, GPolyVar>(this.ringC, monoid);
            FlatteningVisitor<T, GPolyVar> innerFv  = new FlatteningVisitor<T, GPolyVar>(flatRing);
            OPCExportVisitor<T> export = new OPCExportVisitor<T>(innerFv, fv, new PLAIN_Util());
            newConstraint.visit(export);
            System.err.println(interpretation);
            System.err.println(export);
        }

        opcToFormula.applyToWithCleanup(newConstraint);
        aborter.checkAbortion();
        Formula<None> formula = opcToFormula.getFormulaWithCleanup();
        assert(formula != null);

        aborter.checkAbortion();

        // add additional formulae
        formula = formulaFactory.buildAnd(formula, binarizer.getRangeConstraint());

        // specific code for arctic matrices
        if (this.minValue.signum() >= 0) {
            // non-BZ: interpretations must be somewhere finite
            Formula<None> finitenessConstraint = binarizer.getFinitenessConstraints(
                    interpretation.getFirstComponentCoeffNames());
            formula = formulaFactory.buildAnd(formula, finitenessConstraint);
        } else {
            // BZ: interpretations must be positive
            Formula<None> positivenessConstraint;
            if (this.absPos) {
                // absolute: the first entry of the constant vector must be >= 0
                // (RTA'08, Koprowski and Waldmann)
                positivenessConstraint = binarizer.getAbsolutePositivenessConstraints(
                    interpretation.getFirstComponentConstantNames());
            } else {
                // somewhere: interpretations must be somewhere positive
                // (RTA-TLCA'14, Sternagel and Thiemann)
                positivenessConstraint = binarizer.getSomewherePositivenessConstraints(
                    interpretation.getFirstComponentCoeffNames());
            }
            formula = formulaFactory.buildAnd(formula, positivenessConstraint);
        }

        if (this.binarizer instanceof ExoticIntUnarizer) {
            formula = formulaFactory.buildAnd(formula,
                    ((ExoticIntUnarizer<T>)this.binarizer).getPrefixCondition());
        }

        nanos2 = System.nanoTime();
        if (PMatroExoticSolver.log.isLoggable(Level.FINE)) {
            PMatroExoticSolver.log.fine("Encoding Exotic Matrix Constraints to SAT took "
                    + (nanos2-nanos1)/1000000 + " ms.\n");
        }
        aborter.checkAbortion();

        // feed the complete formula to a SAT checker and build a
        // variable substitution from the result
        nanos1 = System.nanoTime();
        SATChecker satChecker = this.engine.getSATChecker();
        int[] model;
        try {
            model = satChecker.solve(formula, aborter);
        } catch (SolverException e) {
            model = null;
        }
        nanos2 = System.nanoTime();
        if (PMatroExoticSolver.log.isLoggable(Level.FINE)) {
            PMatroExoticSolver.log.fine("SAT solving took "
                    + (nanos2-nanos1)/1000000 + " ms.\n");
        }

        if (model == null) {
            return null;
        }
        aborter.checkAbortion();
        binarizer.setInterpretation(model);
        Map<GPolyVar, T> substitution = binarizer.getSubstitution();
        interpretation = interpretation.specialize(substitution,
                this.ringC.one(), aborter);

        GPolyFlatRing<T, GPolyVar> innerFlatRing =
            new SimpleGPolyFlatRing<T, GPolyVar>(this.ringC, monoid);
        FlatteningVisitor<T, GPolyVar> fvInner =
            new FlatteningVisitor<T, GPolyVar>(innerFlatRing);
        aborter.checkAbortion();
        PMATRO<T> solvingOrder = new PMATROExoticInt<T>(
                interpretation, matrixOrderPolyFactory, fvInner, fv, this.coeffOrder);
        return solvingOrder;
    }

    /**
     * Set this to true to search for an extended monotone algebra
     * (for RRR/MRR).
     */
    public void setExtendedMonotone(boolean extendedMonotone) {
        this.extendedMonotone = extendedMonotone;
    }
}
