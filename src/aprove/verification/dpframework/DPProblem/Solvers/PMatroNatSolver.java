package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.PMATRO.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.Nat.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.PolyMatrices.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

/**
 * A generic solver for matrix interpretations. This is fully functional
 * and must be extended only in special cases.
 *
 * Not reentrant. In practice one should use exactly one of the implemented
 * interfaces.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PMatroNatSolver implements QActiveSolver, RRRSolver, RRRMuSolver, SCNPOrderEncoder {

    /**
     * A factory to obtain a SAT solver that is used to find an interpretation.
     */
    private final Engine engine;

    /**
     * The dimension of the matrices to use.
     */
    private final int dimension;

    /**
     * Set of mu constraints:
     * For every function symbol, stores the parameters that must be
     * monotone. Other parameters can be non-monotone.
     * Set to null if not used.
     */
    private ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu;

    /**
     * The highest allowed coefficient value.
     */
    private final BigIntImmutable maxValue;

    /**
     * Do we use bounded arithmetic for the polynomials?
     * (Currently this is the case iff productBits > 0 or sumBits > 0)
     */
    private final boolean useBoundedArithmetic;

    /**
     * The (semi-)ring the coefficients belong to.
     */
    private final Semiring<BigIntImmutable> ringC =
        new BigIntImmutableRing();

    /**
     * An order for the coefficients.
     */
    private final CoeffOrder<BigIntImmutable> coeffOrder =
        new BigIntImmutableOrder();

    /**
     * A binarizer to obtain binary representations of coefficients.
     */
    private final Binarizer<BigIntImmutable> binarizer;

    /**
     * A factory for PolyCircuits representing the SAT encoding of constraints.
     */
    private final CircuitFactory circuitFactory;

    /**
     * Use collapsing interpretations for applications of DP root symbols
     * (i.e., to numbers, not to vectors of numbers) if applicable?
     */
    private final boolean collapse;

    /**
     * Some information about the specific interpretation used.
     */
    private final String description;

    /**
     * Citations referring to the specific interpretation used.
     */
    private final List<Citation> citations;

    // framework-related ingredients
    private final ConstraintFactory<BigIntImmutable> constraintFactory;

    private final FullSharingFactory<BigIntImmutable, GPolyVar> matrixPolyFactory;
    private final FullSharingFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> matrixBigPolyFactory;
    private final OrderPolyFactory<BigIntImmutable> matrixOrderPolyFactory;
    private final PolyMatrixFactory<BigIntImmutable> matrixFactory;

    private final CMonoid<GMonomial<GPolyVar>> monoid;
    private final GPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outerFlatRing;
    private final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fv;

    private NatPolyMatrixInterpretation interpretation;

    private final FormulaFactory<None> formulaFactory;

    public PMatroNatSolver(
            final Engine engine,
            final int dimension,
            final BigIntImmutable maxValue,
            final BigIntImmutable maxSumValue,
            final BigIntImmutable maxProductValue,
            final boolean collapse,
            final String description,
            final List<Citation> citations) {
        this.engine = engine;
        this.dimension = dimension;
        this.maxValue = maxValue;
        FormulaFactory<None> formulaFactory =
            new aprove.verification.oldframework.PropositionalLogic.Formulae.FullSharingFactory<None>();

        if (maxSumValue.getBigInt().signum() > 0
                || maxProductValue.getBigInt().signum() > 0) {
            BoundedNatCircuitFactory boundedCircuitFactory =
                BoundedNatCircuitFactory.create(formulaFactory,
                        maxSumValue, maxProductValue);
            this.useBoundedArithmetic = true;
            this.binarizer = new NatBinarizer(boundedCircuitFactory);
            boundedCircuitFactory.setBinarizer(this.binarizer);
            this.circuitFactory = boundedCircuitFactory;
        }
        else {
            this.circuitFactory = new NatCircuitFactory(formulaFactory);
            this.binarizer = new NatBinarizer(this.circuitFactory);
            this.useBoundedArithmetic = false;
        }
        this.collapse = collapse;
        this.description = description;
        this.citations = citations;

        // create all necessary factories and such
        //   -- this used to reside in "doSolve"
        this.constraintFactory = new SimpleFactory<BigIntImmutable>();

        this.matrixPolyFactory = new FullSharingFactory<BigIntImmutable, GPolyVar>();
        this.matrixBigPolyFactory =
            new FullSharingFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>();
        this.matrixOrderPolyFactory =
            new OrderPolyFactory<BigIntImmutable>(this.matrixBigPolyFactory, this.matrixPolyFactory);
        this.matrixFactory =
            new PolyMatrixFactory<BigIntImmutable>(this.matrixOrderPolyFactory, this.dimension);

        this.monoid = new GMonomialMonoid<GPolyVar>();
        this.outerFlatRing =
            new SimpleGPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(this.matrixPolyFactory, this.monoid);
        this.fv = new FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(this.outerFlatRing);
        this.interpretation = null;
        this.formulaFactory = this.binarizer.getFormulaFactory();
    }

    /**
     * Try to solve the given problem defined by rule constraints.
     * @param pRules The pairs (P).
     * @param rules The rules with the corresponding QActiveCondition.
     * @param active not used.
     * @param allstrict this parameter is not used, use strategy parameter
     * @param aborter The aborter is used to abort calculations after some time.
     * @throws AbortionException Thrown when the aborter gets active.
     * @return An order solving the problem if it can be found.
     */
    @Override
    public QActiveOrder solveQActive(
            final Set<? extends GeneralizedRule> P,
            final Map<? extends GeneralizedRule, QActiveCondition> R,
            final boolean active,
            final boolean allstrict,
            final Abortion aborter)
            throws AbortionException {
        return this.doSolve(P, R, allstrict, false, null, aborter);
    }

    @Override
    public boolean isRRRApplicable(Set<Rule> R) {
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRR(Set<Rule> R, Abortion aborter)
            throws AbortionException {
        return this.doSolve(R, Collections.<Rule, QActiveCondition>emptyMap(),
                false, true, null, aborter);
    }

    @Override
    public boolean isRRRMuApplicable(Set<Rule> R,
            ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu) {
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRRMu(Set<Rule> R,
            ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu,
            Abortion aborter) throws AbortionException {
        return this.doSolve(R, Collections.<Rule, QActiveCondition>emptyMap(),
                false, true, mu, aborter);
    }

    /**
     * Try to solve the given problem defined by rule constraints.
     * @param P The pairs (P).
     * @param R The rules with the corresponding QActiveCondition.
     * @param allstrict true: orient all of P strictly, false: just one of them
     * @param extendedMonotone
     *      Whether to search for an extended monotone algebra (with > and >= being
     *      monotone) or a weakly monotone one (with only >= being monotone).
     *      Extended monotone algebras are used for RRR/MRR.
     * @param mu
     *      Set of mu constraints:
     *      For every function symbol, stores the parameters that must be
     *      monotone. Other parameters can be non-monotone.
     *      Set to null if not used.
     * @param aborter The aborter is used to abort calculations after some time.
     * @throws AbortionException Thrown when the aborter gets active.
     * @return An order solving the problem if it can be found.
     */
    private QActiveOrder doSolve(final Set<? extends GeneralizedRule> P,
            final Map<? extends GeneralizedRule, QActiveCondition> R, final boolean allstrict,
            final boolean extendedMonotone,
            final ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu,
            final Abortion aborter) throws AbortionException {

        // compute symbols for which collapsing interpretations
        // will be used
        Set<? extends GeneralizedRule> rRules = R.keySet();
        Set<FunctionSymbol> collapsingSyms = this.getCollapsingSyms(P, rRules);

        Set<FunctionSymbol> signature = aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(P);
        signature.addAll(aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(rRules));

        aborter.checkAbortion();
        this.initInterpretation(signature, collapsingSyms, allstrict);
        aborter.checkAbortion();

        // generate constraints
        OrderPolyConstraint<BigIntImmutable> usableRulesConstraint =
            this.interpretation.getActiveRuleConstraints(R, aborter);
        aborter.checkAbortion();

        OrderRelation rel = OrderRelation.GR;
        Set<Constraint<TRSTerm>> pConstraints = Constraint.fromRules(P, rel);
        aborter.checkAbortion();
        OrderPolyConstraint<BigIntImmutable> newConstraint =
            this.interpretation.fromTermConstraints(pConstraints, aborter);
        newConstraint = this.constraintFactory.createAnd(newConstraint, usableRulesConstraint);
        if (extendedMonotone) {
            newConstraint = this.constraintFactory.createAnd(newConstraint,
                    this.interpretation.getExtendedMonotonicityConstraint());
        }
        aborter.checkAbortion();

        // transform the constraint into a propositional formula
        PolyToCircuitConverter<BigIntImmutable, GPolyVar> polyToCircuit =
            new PolyToCircuitConverter<BigIntImmutable, GPolyVar>(
                    this.circuitFactory, this.binarizer, this.maxValue);
        OPCtoFormulaConverter<BigIntImmutable> opcToFormula =
            new OPCtoFormulaConverter<BigIntImmutable>(polyToCircuit, this.formulaFactory);
        aborter.checkAbortion();
        opcToFormula.applyToWithCleanup(newConstraint);
        Formula<None> formula = opcToFormula.getFormulaWithCleanup();

        aborter.checkAbortion();

        // add range constraints
        formula = this.formulaFactory.buildAnd(formula,
                this.binarizer.getRangeConstraint());
        if (Globals.useAssertions) {
            assert(formula != null);
        }

        // feed the complete formula to a SAT checker and build a
        // variable substitution from the result
        SATChecker satChecker = this.engine.getSATChecker();
        int[] model;
        try {
            model = satChecker.solve(formula, aborter);
        } catch (SolverException e) {
            model = null;
        }
        if (model == null) {
            return null;
        }
        PMATRO<BigIntImmutable> solvingOrder = this.decode(model, aborter);
        return solvingOrder;
    }

    /**
     * @param P
     * @param R
     * @return the symbols for the DP problem (P, R) that can safely
     *  be interpreted over N^1 instead of N^d.
     */
    private Set<FunctionSymbol> getCollapsingSyms(Set<? extends GeneralizedRule> P, Set<? extends GeneralizedRule> R) {
        Set<FunctionSymbol> collapsingSyms = null;
        if (this.collapse) {
            collapsingSyms =
                aprove.verification.dpframework.BasicStructures.CollectionUtils.getTupleSymbols(P, R);
        }
        if (collapsingSyms == null) {
            collapsingSyms = java.util.Collections.emptySet();
        }
        return collapsingSyms;
    }

    private void initInterpretation(Set<FunctionSymbol> signature,
            Set<FunctionSymbol> collapsingSyms, boolean allstrict) {
        // create a new interpretation and interpret all function symbols
        // occurring in the signature
        NatPolyMatrixInterpretation interpretation =
            NatPolyMatrixInterpretation.create(
                    signature, this.ringC, this.fv, this.matrixOrderPolyFactory,
                    this.matrixFactory, this.constraintFactory, this.dimension, allstrict,
                    collapsingSyms, this.description, this.citations, this.mu);
        this.interpretation = interpretation;
    }

    private void initInterpretationSCNP(Set<FunctionSymbol> signature) {
        // SCNP does not collapse anything (from the overall signature,
        // it wouldn't know what), and it is not responsible for dealing
        // with allstrict
        this.initInterpretation(signature,
                Collections.<FunctionSymbol>emptySet(), false);
    }

    // Below are the methods for the SCNPOrderEncoder interface

    @Override
    public PMATRO<BigIntImmutable> decode(int[] satModel, Abortion aborter)
            throws AbortionException {
        PMATRO<BigIntImmutable> solvingOrder;
        this.binarizer.setInterpretation(satModel);
        Map<GPolyVar, BigIntImmutable> substitution = this.binarizer.getSubstitution();
        this.interpretation = this.interpretation.specialize(substitution, this.ringC.one(), aborter);

        aborter.checkAbortion();

        GPolyFlatRing<BigIntImmutable, GPolyVar> innerFlatRing =
            new SimpleGPolyFlatRing<BigIntImmutable, GPolyVar>(this.ringC, this.monoid);
        FlatteningVisitor<BigIntImmutable, GPolyVar> fvInner =
            new FlatteningVisitor<BigIntImmutable, GPolyVar>(innerFlatRing);
        solvingOrder =
            new PMATRO<BigIntImmutable>(this.interpretation, this.matrixOrderPolyFactory,
                    fvInner, this.fv, this.coeffOrder);
        return solvingOrder;
    }

    @Override
    public Formula<None> encode(Constraint<TRSTerm> c, Abortion aborter)
            throws AbortionException {
        OrderPolyConstraint<BigIntImmutable> opc =
            this.interpretation.termConstraintToExistentialOPC(c, aborter);

        // transform the constraint into a propositional formula
        PolyToCircuitConverter<BigIntImmutable, GPolyVar> polyToCircuit =
            new PolyToCircuitConverter<BigIntImmutable, GPolyVar>(
                    this.circuitFactory, this.binarizer, this.maxValue);
        OPCtoFormulaConverter<BigIntImmutable> opcToFormula =
            new OPCtoFormulaConverter<BigIntImmutable>(polyToCircuit, this.formulaFactory);
        aborter.checkAbortion();
        opcToFormula.applyToWithCleanup(opc);
        Formula<None> res = opcToFormula.getFormulaWithCleanup();
        return res;
    }

    @Override
    public Formula<None> encodeQActiveAtom(FunctionSymbol f, int i,
            Abortion aborter) throws AbortionException {
        OrderPolyConstraint<BigIntImmutable> opc =
            this.interpretation.encodeQActiveAtom(f, i, aborter);

        // transform the constraint into a propositional formula
        PolyToCircuitConverter<BigIntImmutable, GPolyVar> polyToCircuit =
            new PolyToCircuitConverter<BigIntImmutable, GPolyVar>(
                    this.circuitFactory, this.binarizer, this.maxValue);
        OPCtoFormulaConverter<BigIntImmutable> opcToFormula =
            new OPCtoFormulaConverter<BigIntImmutable>(polyToCircuit, this.formulaFactory);
        opcToFormula.applyToWithCleanup(opc);
        Formula<None> res = opcToFormula.getFormulaWithCleanup();
        return res;
    }

    @Override
    public FormulaFactory<None> getFormulaFactory() {
        return this.formulaFactory;
    }

    @Override
    public Formula<None> post(Abortion aborter) throws AbortionException {
        Formula<None> res = this.binarizer.getRangeConstraint();
        return res;
    }

    @Override
    public Formula<None> pre(Set<FunctionSymbol> sig, Abortion aborter)
            throws AbortionException {
        this.initInterpretationSCNP(sig);
        return this.formulaFactory.buildConstant(true);
    }

    @Override
    public Formula<None> toFinalFormula(Formula<None> f, Abortion aborter)
            throws AbortionException {
        return f;
    }
}
