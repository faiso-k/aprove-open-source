package aprove.verification.oldframework.IntTRS.Ranking;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Finds a ranking, that includes a TransitionRelation from some symbol f back
 * to f. Please note, that the RankingFinder always has to find well-founded
 * rankings. This is somehow similar to the method of Rybalchenko & Podelski,
 * but it also takes existential quantified variables into account. Furthermore
 * it may also works with polynomial, not with matrices.
 * @author Matthias Hoelzel
 */
public class RankingFinder {
    /** The relation we have to include. */
    private final TransitionRelation obligation;

    /** The coefficients we use to infer the lower bound. */
    private List<String> lambdaBound;

    /** The coefficients we use to infer the "decreasing" of the interpretation. */
    private List<String> lambdaDelta;

    /** The coefficient for the rankings. */
    private List<String> mu;

    /**
     * The result of multiplying lambdaBound and the polynomials from the
     * constraints.
     */
    private VarPolynomial lambdaBoundYield;

    /** See lambdaBoundYield. */
    private VarPolynomial lambdaDeltaYield;

    /** The left of lambdaBound's yield. */
    private VarPolynomial lambdaBoundLeftSide;

    /** The left of lambdaDelta's yield. */
    private VarPolynomial lambdaDeltaLeftSide;

    /**
     * Polynomial to compare the result coefficient; needed for inferring the
     * lowerBound.
     */
    private VarPolynomial lowerBoundPoly;

    /**
     * Polynomial to compare the result coefficient; needed for inferring the
     * decrease.
     */
    private VarPolynomial decreasePoly;

    /** List of constraints to be solved. */
    private List<SMTLIBTheoryAtom> constraints;

    /** Result obtained from the SMT-Solver */
    private Pair<YNM, Map<String, String>> smtSolverResult;

    /** The result we want to create */
    private Ranking resultRanking;

    /** Some aborter */
    private final Abortion aborter;

    /** Some name generator */
    private final FreshNameGenerator ng;

    /**
     * Constructor!
     * @param obligationRelation some TransitionRelation to be included in the
     * ranking
     * @param gen some name generator
     * @param abortion some aborter
     */
    public RankingFinder(
        final TransitionRelation obligationRelation,
        final FreshNameGenerator gen,
        final Abortion abortion)
    {
        assert obligationRelation != null : "Null?!";
        assert !obligationRelation.isCertainlyWellFounded() : "Relation is already well-founded!";

        this.obligation = obligationRelation;
        this.ng = gen;
        this.aborter = abortion;
    }

    /**
     * Tries to find a ranking. When this fails, then we return null.
     * @return a Ranking
     * @throws AbortionException can be aborted
     */
    public Ranking findRanking() throws AbortionException {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("ranking");
            l.logln("RankingFinder was invoked to solve:");
            l.logln(this.obligation);
            l.logln();
        }

        this.buildMu();
        this.buildLamdas();
        this.buildPolys();
        this.buildConstraints();
        try {
            this.askSMTSolver();
        } catch (final WrongLogicException e) {
            return null;
        }
        this.createResult();

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("ranking");
            l.logln("RankingFinder created:");
            l.logln(this.resultRanking);
            l.logln();
        }

        return this.resultRanking;
    }

    /**
     * Builds the coefficients for the interpretation.
     */
    private void buildMu() {
        final int size = this.obligation.getStartVariables().size();
        this.mu = new ArrayList<>(size);
        for (int i = 0; i < size; i++) {
            this.mu.add(this.ng.getFreshName("m", false));
        }
    }

    /**
     * Builds the coefficients for the constraints.
     */
    private void buildLamdas() {
        final int numberOfConstraints = this.obligation.getPCS().getConstraints().size();
        this.lambdaBound = new ArrayList<>(numberOfConstraints);
        this.lambdaDelta = new ArrayList<>(numberOfConstraints);

        for (int i = 0; i < numberOfConstraints; i++) {
            this.lambdaBound.add(this.ng.getFreshName("l", false));
            this.lambdaDelta.add(this.ng.getFreshName("l", false));
        }
    }

    /**
     * Builds some polynomials, which are needed to formulate the SMT-Problem.
     */
    private void buildPolys() {
        this.buildYields();
        this.buildTargetPolys();
    }

    /**
     * Builds the yields of lambdaBound & lambdaDelta.
     */
    private void buildYields() {
        final Iterator<GEConstraint> constraintsIterator = this.obligation.getPCS().getConstraints().iterator();
        final Iterator<String> lambdaBoundIterator = this.lambdaBound.iterator();
        final Iterator<String> lambdaDeltaIterator = this.lambdaDelta.iterator();

        this.lambdaBoundYield = VarPolynomial.ZERO;
        this.lambdaDeltaYield = VarPolynomial.ZERO;
        this.lambdaBoundLeftSide = VarPolynomial.ZERO;
        this.lambdaDeltaLeftSide = VarPolynomial.ZERO;

        while (constraintsIterator.hasNext()) {
            final GEConstraint gec = constraintsIterator.next();
            final String curLambdaBound = lambdaBoundIterator.next();
            final String curLambdaDelta = lambdaDeltaIterator.next();

            final VarPolynomial vpLambdaBound = VarPolynomial.createCoefficient(curLambdaBound);
            final VarPolynomial vpLambdaDelta = VarPolynomial.createCoefficient(curLambdaDelta);

            this.lambdaBoundYield = this.lambdaBoundYield.plus(gec.getPoly().times(vpLambdaBound));
            this.lambdaDeltaYield = this.lambdaDeltaYield.plus(gec.getPoly().times(vpLambdaDelta));
            this.lambdaBoundLeftSide =
                this.lambdaBoundLeftSide.plus(VarPolynomial.create(gec.getConstant()).times(vpLambdaBound));
            this.lambdaDeltaLeftSide =
                this.lambdaDeltaLeftSide.plus(VarPolynomial.create(gec.getConstant()).times(vpLambdaDelta));
        }
    }

    /**
     * Builds the polynomial we want to create.
     */
    private void buildTargetPolys() {
        this.lowerBoundPoly = VarPolynomial.ZERO;
        this.decreasePoly = VarPolynomial.ZERO;

        final Iterator<String> muIter = this.mu.iterator();
        final Iterator<TRSVariable> startVarIter = this.obligation.getStartVariables().iterator();
        final Iterator<TRSVariable> endVarIter = this.obligation.getEndVariables().iterator();
        while (muIter.hasNext()) {
            final VarPolynomial curMu = VarPolynomial.createCoefficient(muIter.next());
            final VarPolynomial curStartVar = VarPolynomial.createVariable(startVarIter.next().getName());
            final VarPolynomial curEndVar = VarPolynomial.createVariable(endVarIter.next().getName());

            this.lowerBoundPoly = this.lowerBoundPoly.plus(curMu.times(curStartVar));
            this.decreasePoly = this.decreasePoly.plus(curMu.times(curStartVar.minus(curEndVar)));
        }
    }

    /**
     * Uses the polynomials created above to formulate SMT-Constraints.
     */
    private void buildConstraints() {
        this.constraints = new LinkedList<>();
        this.buildValidityConstraints(this.lambdaBound);
        this.buildValidityConstraints(this.lambdaDelta);
        this.buildResultConstraints(this.lambdaBoundYield.minus(this.lowerBoundPoly));
        this.buildResultConstraints(this.lambdaDeltaYield.minus(this.decreasePoly));
        this.buildStrictDecreasingConstraint();
    }

    /**
     * The yield must be valid. So the lambdas have to be >= 0.
     * @param coefficients current lambda coefficients
     */
    private void buildValidityConstraints(final List<String> coefficients) {
        for (final String coefficient : coefficients) {
            this.constraints.add(SMTLIBRatGE.create(
                SMTLIBRatVariable.create(coefficient),
                SMTLIBRatConstant.create(BigInteger.ZERO)));
        }
    }

    /**
     * The input polynomial should be identically 0; thus, every coefficient has
     * to be 0.
     * @param vp current polynomial
     */
    private void buildResultConstraints(final VarPolynomial vp) {
        for (final SimplePolynomial sp : vp.getVarMonomials().values()) {
            final SMTLIBRatValue ratVal = ToolBox.rewriteSimplePolynomialToSMTLIBRatValue(sp);
            this.constraints.add(SMTLIBRatEquals.create(ratVal, SMTLIBRatConstant.create(BigInteger.ZERO)));
        }
    }

    /**
     * Builds the constraint, ensuring that our interpretation is decreasing.
     */
    private void buildStrictDecreasingConstraint() {
        assert this.lambdaDeltaLeftSide.getVarMonomials().size() == 1 : "The left of lambdaDelta's yield should have only one monomial!";
        final SMTLIBRatValue ratVal =
            ToolBox.rewriteSimplePolynomialToSMTLIBRatValue(this.lambdaDeltaLeftSide.getConstantPart());
        this.constraints.add(SMTLIBRatGT.create(ratVal, SMTLIBRatConstant.create(BigInteger.ZERO)));
    }

    /**
     * Asks the SMT-Solver to generate a solution for the SMT-Problem created
     * above.
     * @throws AbortionException can be aborted
     */
    private void askSMTSolver() throws AbortionException, WrongLogicException {
        final FormulaFactory<SMTLIBTheoryAtom> factory = new FullSharingFactory<>();
        final List<Formula<SMTLIBTheoryAtom>> formulas = new LinkedList<>();
        for (final SMTLIBTheoryAtom atom : this.constraints) {
            formulas.add(factory.buildTheoryAtom(atom));
        }

        final SMTEngine smtEngine = new YicesEngine();

        this.smtSolverResult = smtEngine.solve(formulas, SMTLogic.QF_LRA, this.aborter);
    }

    /**
     * Using the model, which was generated by the SMT-Solver, we can build the
     * wanted interpretation & construct the Ranking-Relation. Furthermore, it
     * adds some additional monotonicity constraints.
     * @throws AbortionException can be aborted
     */
    private void createResult() throws AbortionException {
        if (this.smtSolverResult != null
            && this.smtSolverResult.getKey() == YNM.YES
            && this.smtSolverResult.getValue() != null)
        {
            final Map<String, String> model = this.smtSolverResult.getValue();
            final Map<String, PreciseRational> ratModel = new LinkedHashMap<>(model.size());
            for (final Entry<String, String> entry : model.entrySet()) {
                ratModel.put(entry.getKey(), PreciseRational.parseRational(entry.getValue()));
            }

            final PreciseRational boundValue =
                ToolBox.evaluateSimplePolynomial(this.lambdaBoundLeftSide.getConstantPart(), ratModel);
            final BigInteger boundDenominator = boundValue.getDenominator();

            final PreciseRational deltaRat =
                ToolBox.evaluateSimplePolynomial(this.lambdaDeltaLeftSide.getConstantPart(), ratModel);
            final BigInteger deltaDenominator = deltaRat.getDenominator();

            BigInteger lcm = BigInteger.ONE;
            lcm = this.getLCM(lcm, boundDenominator);
            lcm = this.getLCM(lcm, deltaDenominator);
            for (final String muCoeff : this.mu) {
                lcm = this.getLCM(lcm, ratModel.get(muCoeff).getDenominator());
            }

            final BigInteger newBound = boundValue.getNumerator().multiply(lcm).divide(boundDenominator);
            final BigInteger newDelta = deltaRat.getNumerator().multiply(lcm).divide(deltaDenominator);

            VarPolynomial jamesBound = this.buildInterpretedPolynomial(ratModel, lcm, this.lambdaBoundYield);
            VarPolynomial deltaPoly = this.buildInterpretedPolynomial(ratModel, lcm, this.lambdaDeltaYield);

            final List<TRSVariable> newStartVariables = new LinkedList<>();
            final List<TRSVariable> newEndVariables = new LinkedList<>();
            final LinkedHashMap<String, VarPolynomial> renaming = new LinkedHashMap<>(newStartVariables.size() * 2);

            for (final TRSVariable var : this.obligation.getStartVariables()) {
                final String newName = this.ng.getFreshName(RankingUtil.LEFT_VARIABLE_NAME, false);
                newStartVariables.add(TRSTerm.createVariable(newName));
                renaming.put(var.getName(), VarPolynomial.createVariable(newName));
            }
            for (final TRSVariable var : this.obligation.getEndVariables()) {
                final String newName = this.ng.getFreshName(RankingUtil.RIGHT_VARIABLE_NAME, false);
                newEndVariables.add(TRSTerm.createVariable(newName));
                renaming.put(var.getName(), VarPolynomial.createVariable(newName));
            }

            jamesBound = jamesBound.substituteVariables(renaming, this.aborter);
            deltaPoly = deltaPoly.substituteVariables(renaming, this.aborter);

            final List<GEConstraint> resultConstraints = new LinkedList<>();
            resultConstraints.add(GEConstraint.create(jamesBound, newBound));
            resultConstraints.add(GEConstraint.create(deltaPoly, newDelta));

            this.addMonotonicityConstraints(resultConstraints, renaming);

            final PCS pcs = new PCS(resultConstraints, this.aborter);
            this.resultRanking =
                new Ranking(
                    pcs,
                    this.obligation.getStartSymbol(),
                    newStartVariables,
                    newEndVariables,
                    this.obligation,
                    true,
                    this.aborter);
        }
    }

    /**
     * Adds some monotonicity constraints, that occuring in the obligation
     * relation.
     * @param resultConstraints list of result constraints to be completed
     * @param renaming maps the old variable name to the new correspondings ones
     */
    private void addMonotonicityConstraints(
        final List<GEConstraint> resultConstraints,
        final LinkedHashMap<String, VarPolynomial> renaming)
    {
        final PCS monoPCS = this.obligation.getMonotonicitySystem();
        for (final GEConstraint c : monoPCS.getConstraints()) {
            resultConstraints.add(GEConstraint.create(c.getPoly().substituteVariables(renaming), c.getConstant()));
        }
    }

    /**
     * Constructs the interpreted polynomial.
     * @param ratModel current model
     * @param lcm current lcm, needed to get rid of fractions
     * @param poly current polynomial
     * @return VarPolynomail
     */
    private VarPolynomial buildInterpretedPolynomial(
        final Map<String, PreciseRational> ratModel,
        final BigInteger lcm,
        final VarPolynomial poly)
    {
        VarPolynomial jamesBound = VarPolynomial.ZERO;
        for (final Entry<IndefinitePart, SimplePolynomial> entry : poly.getVarMonomials().entrySet()) {
            final IndefinitePart indefPart = entry.getKey();
            final SimplePolynomial simplePart = entry.getValue();
            final PreciseRational simpleRat = ToolBox.evaluateSimplePolynomial(simplePart, ratModel);
            final BigInteger newCoeff = simpleRat.getNumerator().multiply(lcm).divide(simpleRat.getDenominator());
            jamesBound = jamesBound.plus(ToolBox.createVarPolynomial(SimplePolynomial.create(newCoeff), indefPart));
        }
        return jamesBound;
    }

    /**
     * Calculates the LCM of a and b.
     * @param a BigInteger
     * @param b BigInteger
     * @return another BigInteger
     */
    public BigInteger getLCM(final BigInteger a, final BigInteger b) {
        return a.multiply(b).abs().divide(a.gcd(b));
    }
}
