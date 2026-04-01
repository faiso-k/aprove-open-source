package aprove.verification.dpframework.DPProblem.Processors;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.DPConstraints.AbstractInductionCalculus.*;
import aprove.verification.dpframework.DPConstraints.Implication;
import aprove.verification.dpframework.DPConstraints.Constraint;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.QActiveCondition.*;
import aprove.verification.dpframework.Heuristics.Conditions.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Processor based on Giesl's paper "Proving Termination by Bounded Increase",
 * Theorem 15.
 *
 * @author swiste, cotto
 */
public class QDPNonInfReductionPairProcessor extends QDPProblemProcessor {
    public static int exportCounter = 0;

    private static Logger log =
        Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPNonInfReductionPairProcessor");

    /**
     * The (SAT) engine used to construct the resulting formula.
     *
     */
    private final Engine engine;

    /**
     * The converter SP-Constraints -> SAT.
     */
    private final DiophantineSATConverter dioSatConv;

    /**
     * The maximum value the positive part of a coefficient (-min + p)
     * can take. maxPos is (min+max) such that the maximum value of each
     * (-min + p) coefficient is max.
     */
    private final BigInteger maxPos;

    /**
     * For a value of min the minimal coefficient (for tuple symbols) is -min.
     */
    private final BigInteger min;

    /**
     * The maximum value a positive coefficient without negative option can
     * take (so max*x, not (-min + max)*x).
     */
    private final BigInteger max;

    /**
     * The coefficient min used for (-min + p) as a SimplePolynomial.
     */
    private final SimplePolynomial minPol;

    /**
     * The degree used to interpret tuple symbols. Degree 2 allows x, x^2, xy,
     * but not x^2y (sum of exponents <= degree).
     */
    private final int degreeTuple;

    /**
     * The length of the chain in right direction.
     */
    private final int rightChainCounter;

    /**
     * The length of the chain in left direction.
     */
    private final int leftChainCounter;

    /**
     * Number of Inductions per Equality.
     */
    private final int inductionCounter;

    /**
     * If true at least one tuple coefficient will be negative.
     */
    private final boolean enforceNegative;

    /**
     * If this is set then for each tuple symbol the formula will try to find
     * out if no negative interpretation is used. If this is the case the checks
     * for boundedness will be skipped for that tuple symbol.
     */
    private final boolean detectNonNegative;

    /**
     * See max, used for function symbols with arity 1 or 0.
     */
    private final BigInteger maxForSmall;

    /**
     * See maxPos, used for function symbols with arity 1 or 0.
     */
    private final BigInteger maxPosForSmall;

    /**
     * A constructor only giving this processor a name.
     */
    @ParamsViaArgumentObject
    public QDPNonInfReductionPairProcessor(final Arguments arguments) {
        this.degreeTuple = arguments.degreeTuple;
        this.detectNonNegative = arguments.detectNonNegative;
        this.dioSatConv = arguments.satConverter;
        this.enforceNegative = arguments.enforceNegative;
        this.engine = arguments.engine;
        this.inductionCounter = arguments.inductionCounter;
        this.leftChainCounter = arguments.leftChainCounter;
        this.rightChainCounter = arguments.rightChainCounter;

        this.max = BigInteger.valueOf(arguments.maximum);
        this.maxForSmall = BigInteger.valueOf(arguments.maximumForSmall);
        this.min = BigInteger.valueOf(arguments.minimum);


        this.maxPosForSmall = this.maxForSmall.add(this.min);
        this.maxPos = this.max.add(this.min);
        this.minPol = SimplePolynomial.create(this.min);

    }

    /**
     * Generate a DioVar with range [0,1] and register it in the interval map.
     * @param name The name of the DioVar. A unique number will be added to it.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @return A string which is the complete name of the DioVar.
     */
    private String generateBool(
            final Coeff nc,
            final String name,
            final Map<String, BigInteger> coeffRanges) {
        final String fullName = name + nc.getNext();
        coeffRanges.put(fullName, BigInteger.ONE);
        return fullName;
    }

    /**
     * @param qdp The qdp problem which should be handled.
     * @return true iff this processor can handle the given QDP.
     */
    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return qdp.getInnermost() && qdp.getMinimal();
    }

    /**
     * @param qdp The QDPProblem to be solved.
     * @param aborter The aborter tells the processor to stop when some
     * time limit is hit.
     * @return A result, which is unsuccessful or {P \ P_>, P \ P_bound} with
     * proof.
     * @throws AbortionException when the aborter tells this processor to stop.
     */
    @Override
    protected Result processQDPProblem(final QDPProblem qdp,
            final Abortion aborter) throws AbortionException {
        if (!(this.engine instanceof SatEngine)) {
            return null;
        }
        final Map<String, BigInteger> coeffRanges = new LinkedHashMap<String, BigInteger>();
        final Set<TRSTerm> cTerms = new LinkedHashSet<TRSTerm>();
        final Map<FunctionSymbol, Map<Integer, Set<SimplePolynomial>>>
        coefficientTupleMap = new LinkedHashMap<FunctionSymbol,
        Map<Integer, Set<SimplePolynomial>>>();
        final Map<FunctionSymbol, Map<Integer, SimplePolynomial>> coefficientMap =
            new LinkedHashMap<FunctionSymbol, Map<Integer, SimplePolynomial>>();
        final Map<FunctionSymbol, Map<Integer, SimplePolynomial>> positionIsAsc =
            new LinkedHashMap<FunctionSymbol, Map<Integer, SimplePolynomial>>();
        final Map<FunctionSymbol, Map<Integer, SimplePolynomial>> positionIsDesc =
            new LinkedHashMap<FunctionSymbol, Map<Integer, SimplePolynomial>>();
        final Map<Rule, String> strictRules = new LinkedHashMap<Rule, String>();
        final Map<Rule, String> boundRules = new LinkedHashMap<Rule, String>();
        final Interpretation interpretation = Interpretation.create();

        int inductionCounter = this.inductionCounter;
        // EXPERIMENTAL REDUCTION OF INDUCTIONCOUNTER
        {
            final Map<Rule, Set<Position>> map = QDPConditionChecker.computeMapOfPositionsWithCondition(qdp);
            final ImmutableSet<FunctionSymbol> defs = qdp.getRwithQ().getDefinedSymbolsOfR();
            int minInds = 1;
            for (final Map.Entry<Rule, Set<Position>> entry : map.entrySet()) {
                final Rule dp = entry.getKey();
                for (final Position p : entry.getValue()) {
                    final TRSTerm tp = dp.getRight().getSubterm(p);
                    for (final TRSTerm s : tp.getSubTerms()) {
                        if (s instanceof TRSFunctionApplication) {
                            final TRSFunctionApplication sApp = (TRSFunctionApplication) s;
                            if (defs.contains(sApp.getRootSymbol())) {
                                minInds++;
                            }
                        }
                    }
                }
            }
            if (minInds < inductionCounter) {
                inductionCounter = minInds;
            }
        }
        // END EXPERIMENTAL
        Options options =
            new Options(this.leftChainCounter, this.rightChainCounter,
                    inductionCounter, 0);
        ConstraintsCache<Rule> constraintsCache = qdp.getConstraintsCache();
        InductionCalculusProof icProof;
        if (this.leftChainCounter == -1 && this.rightChainCounter == -1 && inductionCounter == -1) {
            if (constraintsCache.isEmpty()) {
                return ResultFactory.unsuccessful();
            }
            options = constraintsCache.getOptions();
        }
        if (constraintsCache.needsRefresh(options)) {
            icProof = new InductionCalculusProof(qdp, options);
            final InductionCalculus ic =
                new InductionCalculus(qdp, icProof, options, aborter);
            constraintsCache = ic.generateConstraintsCache();
        } else {
            icProof = constraintsCache.getProofForP(qdp);
        }

        final int apInds = constraintsCache.getAppliedInductions();
        final int realImps = constraintsCache.countRealImplications();
        QDPNonInfReductionPairProcessor.log.log(Level.INFO, apInds + " inductions were applied. Resulting in "
                + realImps + " real implications.\n");

        if (apInds > 0 &&  realImps == 0) {
            QDPNonInfReductionPairProcessor.log.log(Level.INFO, apInds + " inductions were applied but no implication was generated.");
            //exportDirectly2(qdp,icProof,icProof.getOptions());
            return ResultFactory.unsuccessful();
        }

        aborter.checkAbortion(); // ic.simplify() might take ages

        final Map<Rule, List<Implication>> problemMap =
            constraintsCache.getProblemMap();
        final Result result = this.solveProblems(qdp, constraintsCache, problemMap,
                aborter, icProof, coeffRanges, interpretation, cTerms,
                strictRules, boundRules, coefficientTupleMap,
                coefficientMap, positionIsAsc, positionIsDesc);
        if (result != null) {
            return result;
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    public static void exportDirectly(final QDPProblem qdp, final Proof proof, final Options options) {
        QDPNonInfReductionPairProcessor.exportCounter++;
        final String name = "/tmp/";
        try {
            final String d = System.nanoTime() + "";
            final FileWriter fw = new FileWriter(name + d + ".qdp");
            fw.write("(COMMENT " + options + ")\n");
            fw.write(qdp.toExternString());
            fw.close();
            final FileWriter fwh = new FileWriter(name + d + ".html");
            fwh.write(proof.export(new HTML_Util()));
            fwh.close();
        } catch (final Exception e) {
            System.err.println("Direct Export " + name + " export error");
            e.printStackTrace();
        }
    }

    /**
     * @param constraintsCache The cache containing information about the
     * constraints.
     * @param qdp The QDPProblem to be solved.
     * @param problemMap A map containing all (simplified) constraints, where
     * one has to be in P_> and all others in P_\geq, at least one has to be in
     * P_bound
     * @return A proof defining the solution (null if no solution was found).
     * @param aborter The Aborter which may kill this processor after some time.
     * @param icProof The proof giving information about the induction steps.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param strictRules Collect the constraints (value) that have to be
     * fulfilled such that the rule (map's key) is in P_>.
     * @param boundRules Collect the constraints (value) that have to be
     * fulfilled such that the rule (map's key) is in P_bound.
     * @param coefficientTupleMap Collect the DioVars that are part of the
     * coefficients of tuple function symbols.
     * @param coefficientMap Collect the DioVars that are coefficients of
     * non-tuple function symbols.
     * @param cTerms Collect the terms t that appear in "t >= c" for the fresh
     * function symbol c. Based on these terms c will be defined later.
     * @param positionIsDesc A map from tuple symbols and positions to a
     * simple polynomial. It will be guaranteed that if f is decreasing at the
     * i-th position then the simple polynomial will be greater 0. (And if it
     * is not decreasing then it may be 0 or negative).
     * @param positionIsAsc a map from tuple symbols and positions to a simple
     * polynomial. It will be guaranteed that if f is increasing at the i-th
     * position then the simple polynomial will be greater 0. (And if it is not
     * increasing then it may be 0 or negative).
     * @throws AbortionException The Aborter kills this processor.
     */
    private Result solveProblems(
            final QDPProblem qdp,
            final ConstraintsCache<Rule> constraintsCache,
            final Map<Rule, List<Implication>> problemMap,
            final Abortion aborter,
            final InductionCalculusProof icProof,
            final Map<String, BigInteger> coeffRanges,
            final Interpretation interpretation,
            final Set<TRSTerm> cTerms,
            final Map<Rule, String> strictRules,
            final Map<Rule, String> boundRules,
            final Map<FunctionSymbol, Map<Integer, Set<SimplePolynomial>>>
                coefficientTupleMap,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                coefficientMap,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                positionIsAsc,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                positionIsDesc)
            throws AbortionException {
        // prepare interpretation for tuple symbols
        final TRSFunctionApplication c = icProof.getC();
        final Coeff nc = new Coeff();
        final FunctionSymbol cSym = c.getRootSymbol();

        // this collection stores all diophantine constraints that have to be
        // fulfilled
        final int listSize = 200;
        final Collection<Diophantine> dioCollection =
            new ArrayList<Diophantine>(listSize);

        Map<FunctionSymbol, SimplePolynomial> nonNegativeMap = null;
        if (this.detectNonNegative) {
            nonNegativeMap =
                new LinkedHashMap<FunctionSymbol, SimplePolynomial>();
        }

        this.addInterpretation(nc, cSym, true, coeffRanges, interpretation,
                coefficientTupleMap, coefficientMap, dioCollection,
                nonNegativeMap);

        final Set<FunctionSymbol> headSymbols = qdp.getHeadSymbols();

        for (final FunctionSymbol f : headSymbols) {
            this.addInterpretation(nc, f, true, coeffRanges, interpretation,
                    coefficientTupleMap, coefficientMap, dioCollection,
                    nonNegativeMap);
        }

        final int degreeMinusTwo = -2;
        final Set<FunctionSymbol> boundedSymbols;
        if (this.min.signum() <= 0 || this.degreeTuple == degreeMinusTwo) {
            boundedSymbols = headSymbols;
        } else {
            boundedSymbols = null;
        }

        aborter.checkAbortion();

        // prepare interpretation for other symbols in P cup U(P,R)
        // remark that head symbols will not be overwritten, as
        // addInterpretation does nothing if an interpretation for "f" is
        // already present
        for (final FunctionSymbol f : CollectionUtils.getFunctionSymbols(qdp.getP())) {
            this.addInterpretation(nc, f, false, coeffRanges, interpretation,
                    coefficientTupleMap, coefficientMap, dioCollection,
                    nonNegativeMap);
        }

        for (final FunctionSymbol f
                : CollectionUtils.getFunctionSymbols(qdp.getUsableRules())) {
            this.addInterpretation(nc, f, false, coeffRanges, interpretation,
                    coefficientTupleMap, coefficientMap, dioCollection,
                    nonNegativeMap);
        }

        // also add all functionSymbols found in the constraints, because
        // they might include some functionSymbol that is neither in P nor in R.
        for (final List<Implication> list : problemMap.values()) {
            for (final Implication imp : list) {
                for (final FunctionSymbol f : imp.getFunctionSymbols()) {
                    this.addInterpretation(nc, f, false, coeffRanges,
                            interpretation, coefficientTupleMap, coefficientMap,
                            dioCollection, nonNegativeMap);
                }
            }
        }

        final Map<Rule, QActiveCondition> active =
            qdp.getQUsableRulesCalculator().getActiveConditions(qdp.getP());

        // generate DioVars denoting that some position of a tuple symbol is
        // ascending
        this.generateTuplePositionConstraints(nc, dioCollection, coeffRanges,
                coefficientTupleMap, coefficientMap, positionIsAsc,
                positionIsDesc);

        // handle the case where enforceNegative is true, so at least one
        // tuple coefficient must be negative
        this.generateEnforceNegative(nc, dioCollection, coeffRanges,
                coefficientTupleMap);

        aborter.checkAbortion();

        // generate constraints for usable rules
        this.generateUsableRules(nc, active, dioCollection, coeffRanges, interpretation,
                positionIsAsc, positionIsDesc, coefficientMap, aborter);

        aborter.checkAbortion();

        this.generateStrictNonStrictBound(nc, problemMap, dioCollection, coeffRanges,
                interpretation, cTerms, strictRules, boundRules,
                boundedSymbols, nonNegativeMap, aborter);

        aborter.checkAbortion();

        final Result result = this.solveFormula(dioCollection, qdp, aborter, problemMap,
                constraintsCache, active, icProof, coeffRanges, interpretation,
                cTerms, strictRules, boundRules, c, boundedSymbols);
        return result;
    }

    /**
     * @param dioCollection The collection where all diophantine constraints
     * are stored.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param coefficientTupleMap Collect the DioVars that are coefficients of
     * non-tuple function symbols.
     */
    private void generateEnforceNegative(
            final Coeff nc,
            final Collection<Diophantine> dioCollection,
            final Map<String, BigInteger> coeffRanges,
            final Map<FunctionSymbol, Map<Integer,
                Set<SimplePolynomial>>> coefficientTupleMap) {
        if (!this.enforceNegative) {
            return;
        }

        final Set<SimplePolynomial> alternatives =
            new LinkedHashSet<SimplePolynomial>(0);

        for (final Map<Integer, Set<SimplePolynomial>> value
                : coefficientTupleMap.values()) {
            for (final Set<SimplePolynomial> polys : value.values()) {
                for (final SimplePolynomial poly : polys) {
                    SimplePolynomial constraint = this.minPol.minus(poly);

                    final String isNegative =
                        this.generateBool(nc, "ISNEGATIVE_", coeffRanges);
                    final SimplePolynomial isNegativePoly =
                        SimplePolynomial.create(isNegative);

                    // X(n-a) + (1-X) > 0
                    constraint = constraint.times(isNegativePoly);
                    constraint = constraint.plus(SimplePolynomial.ONE);
                    constraint = constraint.minus(isNegativePoly);
                    alternatives.add(isNegativePoly);

                    final Diophantine dio =
                        Diophantine.create(constraint, ConstraintType.GT);
                    dioCollection.add(dio);
                }
            }
        }

        SimplePolynomial atLeastOne = SimplePolynomial.ZERO;
        for (final SimplePolynomial alternative : alternatives) {
            atLeastOne = atLeastOne.plus(alternative);
        }
        final Diophantine dio = Diophantine.create(atLeastOne, ConstraintType.GT);
        dioCollection.add(dio);
    }

    /**
     * Convert the diophantine constraints to a sat formula and try to solve it.
     * @param dioCollection The collection where all diophantine constraints
     * are stored.
     * @param qdp The QDPProblem to be solved.
     * @param aborter The aborter that may kill this processor.
     * @param problemMap The map containing the constraints found for some rule.
     * @param constraintsCache The cache containing information about the
     * constraints.
     * @param active Information about active rules.
     * @param icProof The proof giving information about the induction steps.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param cTerms Collect the terms t that appear in "t >= c" for the fresh
     * function symbol c. Based on these terms c will be defined later.
     * @param strictRules Collect the constraints (value) that have to be
     * fulfilled such that the rule (map's key) is in P_>.
     * @param boundRules Collect the constraints (value) that have to be
     * fulfilled such that the rule (map's key) is in P_bound.
     * @param c The term of the fresh function symbol 'c'.
     * @param boundedSymbols  The set of function symbols of that we know that
     *   it is always bounded, i.e. if t = f(..) and f in boundedSymbols then
     *   Pol(t) is bounded. May be null.
     * @throws AbortionException is thrown when the aborter kills this
     * processor.
     * @return The result of the computation.
     */
    private Result solveFormula(
            final Collection<Diophantine> dioCollection,
            final QDPProblem qdp,
            final Abortion aborter,
            final Map<Rule, List<Implication>> problemMap,
            final ConstraintsCache<Rule> constraintsCache,
            final Map<Rule, QActiveCondition> active,
            final InductionCalculusProof icProof,
            final Map<String, BigInteger> coeffRanges,
            final Interpretation interpretation,
            final Set<TRSTerm> cTerms,
            final Map<Rule, String> strictRules,
            final Map<Rule, String> boundRules,
            final TRSTerm c,
            final Set<FunctionSymbol> boundedSymbols) throws AbortionException {
        final int dioSize = dioCollection.size();
        final FullSharingFactory<Diophantine>factory =
            new FullSharingFactory<Diophantine>();

        final List<Formula<Diophantine>> formulaCollection =
            new ArrayList<Formula<Diophantine>>(dioSize);
        for (final Diophantine dio : dioCollection) {
            formulaCollection.add(factory.buildTheoryAtom(dio));
        }

        aborter.checkAbortion();
        final Formula<Diophantine> fullFormula =
            factory.buildAnd(formulaCollection);

        aborter.checkAbortion();

        final FormulaFactory<None> formulaFactory =
            ((SatEngine) this.engine).getFormulaFactory();
        BigInteger maxValue = this.maxPos;
        if (this.maxPosForSmall.compareTo(this.maxPos) > 0) {
            maxValue = this.maxPosForSmall;
        }
        final PoloSatConverter converter = this.dioSatConv.getPoloSatConverter(
                formulaFactory, coeffRanges, maxValue);

        final SatSearch satSearcher = SatSearch.create(this.engine, converter);
        final Map<String, BigInteger> solution =
            satSearcher.search(fullFormula, aborter);

        if (solution != null) {
            return this.constructProof(interpretation, solution, cTerms, problemMap,
                    boundedSymbols, qdp, strictRules, boundRules, c, icProof,
                    constraintsCache, active, aborter);
        } else {
            return null;
        }
    }

    /**
     * Use the solution found by the SAT solver and find all strict/bound rules.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param solution The solution for the SAT problem.
     * @param cTerms Collect the terms t that appear in "t >= c" for the fresh
     * function symbol c. Based on these terms c will be defined later.
     * @param problemMap The map containing the constraints found for some rule.
     * @param boundedSymbols The set of function symbols of that we know that
     *   it is always bounded, i.e. if t = f(..) and f in boundedSymbols then
     *   Pol(t) is bounded. May be null.
     * @param qdp The QDPProblem to be solved.
     * @param strictRules Collect the constraints (value) that have to be
     * fulfilled such that the rule (map's key) is in P_>.
     * @param boundRules Collect the constraints (value) that have to be
     * fulfilled such that the rule (map's key) is in P_bound.
     * @param c The term of the fresh function symbol 'c'.
     * @param icProof The proof giving information about the induction steps.
     * @param constraintsCache The cache containing information about the
     * constraints.
     * @param active Information about active rules.
     * @return The new QDPProblem(s).
     */
    private Result constructProof(
            final Interpretation interpretation,
            final Map<String, BigInteger> solution,
            final Set<TRSTerm> cTerms,
            final Map<Rule, List<Implication>> problemMap,
            final Set<FunctionSymbol> boundedSymbols,
            final QDPProblem qdp,
            final Map<Rule, String> strictRules,
            final Map<Rule, String> boundRules,
            final TRSTerm c,
            final InductionCalculusProof icProof,
            final ConstraintsCache<Rule> constraintsCache,
            final Map<Rule, QActiveCondition> active,
            final Abortion aborter) throws AbortionException {
        final Interpretation inter = interpretation.specialize(solution, BigInteger.ZERO);

        final BigInteger cNum =
            inter.interpretTerm(c, aborter).getConstantPart().getNumericalAddend();
        BigInteger minConstant = cNum;
        for (final TRSTerm term : cTerms) {
            final BigInteger constant = inter.interpretTerm(term, aborter).
                getConstantPart().getNumericalAddend();
            if (constant.compareTo(minConstant) < 0) {
                minConstant = constant;
            }
        }

        Interpretation newInterpretation;
        if (minConstant.compareTo(cNum) == 0) {
            newInterpretation = inter;
        } else {
            // create a new interpretation with the correct value for
            // POL(c).
            newInterpretation = Interpretation.create();
            final FunctionSymbol cSym = ((TRSFunctionApplication) c).getRootSymbol();
            newInterpretation.put(cSym , VarPolynomial.create(minConstant));
            for (final Map.Entry<FunctionSymbol, VarPolynomial> entry
                    : inter.getPol().entrySet()) {
                final FunctionSymbol funcSym = entry.getKey();
                final VarPolynomial varPol = entry.getValue();
                if (newInterpretation.get(funcSym) == null) {
                    newInterpretation.put(funcSym, varPol);
                }
            }
        }

        // the SAT solver might give a solution where the interpretation is
        // very strong, but the information about the strict/bound rules is
        // too weak (incomplete, but correct). Try to maximize this solution
        // with the found interpretation.
        final Pair<Set<Rule>, Set<Rule>> finerSolution =
            this.getFinerSolution(newInterpretation, problemMap, c,
                    boundedSymbols, aborter);
        final Set<Rule> fineStrict = finerSolution.x;
        final Set<Rule> fineBound = finerSolution.y;

        final Set<Rule> fineNotStrict = new LinkedHashSet<Rule>(qdp.getP());
        fineNotStrict.removeAll(fineStrict);
        final Set<Rule> fineNotBound = new LinkedHashSet<Rule>(qdp.getP());
        fineNotBound.removeAll(fineBound);

        if (Globals.useAssertions) {
            // check if the SAT solution is a subset of the real solution
            final Set<Rule> strictPRules = new LinkedHashSet<Rule>();
            final Set<Rule> boundPRules = new LinkedHashSet<Rule>();
            for (final Rule rule : qdp.getP()) {
                if (strictRules.containsKey(rule)) {
                    final String dioStrict = strictRules.get(rule);
                    if (solution.containsKey(dioStrict)) {
                        if (solution.get(dioStrict).intValue() == 1) {
                            strictPRules.add(rule);
                        }
                    }
                }
                if (boundRules.containsKey(rule)) {
                    final String dioBound = boundRules.get(rule);
                    if (solution.containsKey(dioBound)) {
                        if (solution.get(dioBound).intValue() == 1) {
                            boundPRules.add(rule);
                        }
                    }
                }
            }
            assert (fineStrict.containsAll(strictPRules));
            assert (fineBound.containsAll(boundPRules));
        }

        final Map<Rule, QActiveCondition.Direction> usableRules =
            this.getAndCheckUsableRules(
                    newInterpretation,
                    active,
                    qdp.getHeadSymbols()
            );


        newInterpretation.setCitation(Citation.NONINF);
        final List<QDPProblem> newQDPsP = new ArrayList<>(2);
        final Proof proof = new NonInfProof(newInterpretation,
                fineStrict, fineBound, usableRules,
                icProof,
                qdp,
 newQDPsP);
        final QDPProblem newQdp =
            qdp.getSameProblemAndFillCache(constraintsCache);

        if (fineNotStrict.containsAll(fineNotBound)) {
            // P_bound superset of P_>
            final ImmutableSet<Rule> immutableRemainingRules =
                ImmutableCreator.create(fineNotStrict);
            final QDPProblem remainingQdp =
                newQdp.getSubProblem(immutableRemainingRules);
            newQDPsP.add(remainingQdp);
            return ResultFactory.proved(
                    remainingQdp, YNMImplication.EQUIVALENT, proof);
        } else if (fineNotBound.containsAll(fineNotStrict)) {
            // P_> superset of P_bound
            final ImmutableSet<Rule> immutableRemainingRules =
                ImmutableCreator.create(fineNotBound);
            final QDPProblem remainingQdp =
                newQdp.getSubProblem(immutableRemainingRules);
            newQDPsP.add(remainingQdp);
            return ResultFactory.proved(
                    remainingQdp, YNMImplication.EQUIVALENT, proof);
        } else {
            // two different problems
        final ImmutableSet<Rule> immutableNotStrictRules
            = ImmutableCreator.create(fineNotStrict);
        final ImmutableSet<Rule> immutableNotBoundRules
            = ImmutableCreator.create(fineNotBound);

        final QDPProblem newQDPWithoutStrict =
            newQdp.getSubProblem(immutableNotStrictRules);
        final QDPProblem newQDPWithoutBound =
            newQdp.getSubProblem(immutableNotBoundRules);
            final Set<QDPProblem> newQDPs = new LinkedHashSet<>(2);
            newQDPsP.add(newQDPWithoutStrict);
            newQDPsP.add(newQDPWithoutBound);
        newQDPs.add(newQDPWithoutStrict);
        newQDPs.add(newQDPWithoutBound);
        return ResultFactory.provedAnd(
                newQDPs, YNMImplication.EQUIVALENT, proof);
        }
    }

    /**
     * Compute the usable rules from the real interpretation.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param active Information about active rules.
     * @param headSymbols The head symbols of the QDP.
     * @return a map from rules to directions where None is
     *   never the value of a rule (then that rule is not
     *   inserted into the map)
     */
    private Map<Rule, Direction> getAndCheckUsableRules(
            final Interpretation interpretation,
            final Map<Rule, QActiveCondition> active,
            final Set<FunctionSymbol> headSymbols
            ) throws AbortionException {
        final Map<Rule, Direction> usableRules = new LinkedHashMap<Rule, Direction>();

        final ExtendedAfs afs = interpretation.getExtendedAfs();
        final QActiveOrder polo = POLO.create(interpretation);
        for (final Map.Entry<Rule, QActiveCondition> ruleActive : active.entrySet()) {
            final QActiveCondition condition = ruleActive.getValue();
            final Direction dir = condition.determineOrientation(afs);
            if (dir != Direction.None) {
                final Rule rule = ruleActive.getKey();
                usableRules.put(rule, dir);
                final OrderRelation relation =
                    dir == Direction.Both ? OrderRelation.EQ : OrderRelation.GE;
                aprove.verification.dpframework.Orders.Constraint<TRSTerm> constraint;
                if (dir == Direction.Reversed) {
                    constraint = aprove.verification.dpframework.Orders.Constraint.create(
                            rule.getRight(), rule.getLeft(), relation);
                } else {
                    constraint = aprove.verification.dpframework.Orders.Constraint.fromRule(
                            rule, relation);
                }
                if (!polo.solves(constraint)) {
                    throw new RuntimeException(
                            "internal bug in non-inf-processor");
                }
            }
        }

        return usableRules;
    }

    /**
     * Verify the interpretation found by the SAT solver and find all
     * strict/bound rules that can be found with the interpretation. The SAT
     * solution can mark some rules as non-strict, although they are strict with
     * the given interpretation.
     * @param inter The non-abstract interpretation found by the SAT solver.
     * @param problemMap The DPs and their corresponding constraints that have
     * to be fulfilled.
     * @param cTerm The fresh function symbol 'c'.
     * @param boundedSymbols The set of function symbols of that we know that
     *   it is always bounded, i.e. if t = f(..) and f in boundedSymbols then
     *   Pol(t) is bounded. May be null.
     * @return Two rule sets, where the first contains _all_ rules that are in
     * P_> and the second _all_ rules that are in P_bound.
     */
    private Pair<Set<Rule>, Set<Rule>> getFinerSolution(
            final Interpretation inter,
            final Map<Rule, List<Implication>> problemMap,
            final TRSTerm cTerm,
            final Set<FunctionSymbol> boundedSymbols,
            final Abortion aborter) throws AbortionException {
        final Set<Rule> strictSet = new LinkedHashSet<Rule>();
        final Set<Rule> boundSet = new LinkedHashSet<Rule>();
        final Pair<Set<Rule>, Set<Rule>> resultPair =
            new Pair<Set<Rule>, Set<Rule>>(strictSet, boundSet);
        final VarPolynomial c = inter.interpretTerm(cTerm, aborter);
        for (final Map.Entry<Rule, List<Implication>> entry : problemMap.entrySet()) {
            final Rule dp = entry.getKey();
            final List<Implication> implications = entry.getValue();
            boolean isStrict = true;
            boolean isBound = true;
            for (final Implication implication : implications) {
                if (isStrict || isBound) {
                    final Pair<Boolean, Boolean> pair =
                        this.interpretImplication(implication, inter, c,
                                boundedSymbols, aborter);
                    isStrict = isStrict && pair.x;
                    isBound = isBound && pair.y;
                }
            }
            if (isStrict) {
                strictSet.add(dp);
            }
            if (isBound) {
                boundSet.add(dp);
            }
        }
        return resultPair;
    }

    /**
     * Check if the implication is strict/bound with the given interpretation.
     * @param implication The implication to check.
     * @param inter A non-abstract interpretation (found by the SAT solver).
     * @param c The fresh function symbol 'c' (interpreted, as VarPoly).
     * @param boundedSymbols The set of function symbols of that we know that
     *   it is always bounded, i.e. if t = f(..) and f in boundedSymbols then
     *   Pol(t) is bounded. May be null.
     * @return Two booleans, meaning the implication is strict/bound.
     */
    private Pair<Boolean, Boolean> interpretImplication(
            final Implication implication,
            final Interpretation inter,
            final VarPolynomial c,
            final Set<FunctionSymbol> boundedSymbols,
            final Abortion aborter) throws AbortionException {
        final Constraint conclusion = implication.getConclusion();
        if (Globals.useAssertions) {
            assert (conclusion.isTermAtom());
        }
        final TermAtom atom = (TermAtom) conclusion;
        if (implication.getConditions().isEmpty()) {
            return this.interpretAtom(atom, inter, c, boundedSymbols, aborter);
        } else {
            final VarPolynomial left = inter.interpretTerm(atom.getLeft(), aborter);
            final FunctionSymbol leftRootSymbol =
                ((TRSFunctionApplication) atom.getLeft()).getRootSymbol();
            final VarPolynomial right = inter.interpretTerm(atom.getRight(), aborter);
            final VarPolynomial leftMinusRight = left.minus(right);
            boolean nonstrict = true;
            boolean strict = true;
            boolean bound = true;
            for (final SimplePolynomial coeff : leftMinusRight.getAllCoefficients()) {
                nonstrict = nonstrict && coeff.allPositive();
            }
            final SimplePolynomial constant = leftMinusRight.getConstantPart();
            strict = strict && !constant.isZero();

            if (boundedSymbols == null
                    || !boundedSymbols.contains(leftRootSymbol)) {
                final VarPolynomial leftMinusC = left.minus(c);
                for (final SimplePolynomial coeff : leftMinusC.getAllCoefficients()) {
                    bound = bound && coeff.allPositive();
                }
            }
            if (!strict || !bound) {
                // look at the conditions
                final ConstraintSet constraints = implication.getConditions();
                for (final Constraint constraint : constraints) {
                    if (Globals.useAssertions) {
                        assert (constraint.isTermAtom());
                    }
                    final TermAtom constr = (TermAtom) constraint;
                    if (!strict || !bound) {
                        final VarPolynomial leftConstr =
                            inter.interpretTerm(constr.getLeft(), aborter);
                        final VarPolynomial rightConstr =
                            inter.interpretTerm(constr.getRight(), aborter);
                        final VarPolynomial leftMinusRightConstr =
                            leftConstr.minus(rightConstr);
                        final VarPolynomial combo =
                            leftMinusRight.minus(leftMinusRightConstr);
                        boolean comboStrict = true;
                        for (final SimplePolynomial coeff
                                : combo.getAllCoefficients()) {
                            comboStrict = comboStrict && coeff.allPositive();
                        }
                        strict = strict || comboStrict;

                        final VarPolynomial comboC = left.minus(leftConstr);
                        boolean comboBound = true;
                        for (final SimplePolynomial coeff
                                : comboC.getAllCoefficients()) {
                            comboBound = comboBound && coeff.allPositive();
                        }

                        bound = bound || comboBound;
                    }
                }
            }
            return new Pair<Boolean, Boolean>(strict, bound);
        }
    }

    /**
     * Check if the atom is strict/bound with the given interpretation.
     * @param atom The atom to check.
     * @param inter A non-abstract interpretation (found by the SAT solver).
     * @param c The fresh function symbol 'c' (interpreted, as VarPoly).
     * @param boundedSymbols The set of function symbols of that we know that
     *   it is always bounded, i.e. if t = f(..) and f in boundedSymbols then
     *   Pol(t) is bounded. May be null.
     * @return Two booleans, meaning the implication is strict/bound.
     */
    private Pair<Boolean, Boolean> interpretAtom(
            final TermAtom atom,
            final Interpretation inter,
            final VarPolynomial c,
            final Set<FunctionSymbol> boundedSymbols,
            final Abortion aborter) throws AbortionException {
        final VarPolynomial left = inter.interpretTerm(atom.getLeft(), aborter);
        final FunctionSymbol leftRootSymbol =
            ((TRSFunctionApplication) atom.getLeft()).getRootSymbol();
        final VarPolynomial right = inter.interpretTerm(atom.getRight(), aborter);
        final VarPolynomial leftMinusRight = left.minus(right);
        final VarPolynomial leftMinusC = left.minus(c);
        if (Globals.useAssertions) {
            // non-strict
            for (final SimplePolynomial coeff : leftMinusRight.getAllCoefficients()) {
                assert (coeff.allPositive());
            }
        }
        final SimplePolynomial constant = leftMinusRight.getConstantPart();
        final boolean strict = !constant.isZero();

        boolean bound = true;
        if (boundedSymbols == null
                || !boundedSymbols.contains(leftRootSymbol)) {
            for (final SimplePolynomial coeff : leftMinusC.getAllCoefficients()) {
                if (bound && !coeff.allPositive()) {
                    bound = false;
                }
            }
        }

        return new Pair<Boolean, Boolean>(strict, bound);
    }

    /**
     * Generate constraints for tuple symbols that ensure some position is
     * ascending/descending.
     * For every variable (x in this example) some information is generated that
     * denotes "the rules that are used in x's place are ascending" or
     * "...descending". For linear interpretations this information is just x's
     * coefficient. For more complicated interpretations a fresh variable is
     * returned and defined using side conditions.
     * @param dioCollection The collection where all diophantine constraints
     * are stored.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param coefficientTupleMap Collect the DioVars that are part of the
     * coefficients of tuple function symbols.
     * @param coefficientMap Collect the DioVars that are coefficients of
     * non-tuple function symbols.
     * @param positionIsAsc Store SPs that denote a specific position is
     * ascending.
     * @param positionIsDesc Store SPs that denote a specific position is
     * descending.
     */
    private void generateTuplePositionConstraints(
            final Coeff nc,
            final Collection<Diophantine> dioCollection,
            final Map<String, BigInteger> coeffRanges,
            final Map<FunctionSymbol, Map<Integer, Set<SimplePolynomial>>>
                coefficientTupleMap,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                coefficientMap,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                positionIsAsc,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                positionIsDesc) {
        for (final Map.Entry<FunctionSymbol, Map<Integer, Set<SimplePolynomial>>>
            entry : coefficientTupleMap.entrySet()) {
            // for every tuple symbol...
            final FunctionSymbol f = entry.getKey();
            final Map<Integer, SimplePolynomial> mapAsc =
                new LinkedHashMap<Integer, SimplePolynomial>();
            final Map<Integer, SimplePolynomial> mapDesc =
                new LinkedHashMap<Integer, SimplePolynomial>();
            positionIsAsc.put(f, mapAsc);
            positionIsDesc.put(f, mapDesc);
            final Map<Integer, Set<SimplePolynomial>> map = entry.getValue();
            final int arity = f.getArity();
            for (int i = 0; i < arity; i++) {
                // for every argument of that symbol...

                // dioSet includes all DioVars a where (a-n) is a coefficient of
                // x, x^2, xy, ...
                final Set<SimplePolynomial> dioSet = map.get(i);

                final int degreeMinusTwo = -2;
                if (this.degreeTuple == degreeMinusTwo) {
                    // Special case for degree -2, where interpretations have
                    // the form ((a-n)x+(b-n)y+(c-n)z)^2 + d-n.
                    // Here we use a safe approximation. In the (a != n) case
                    // we say that it is ascending and descending in x.
                    // (Otherwise all other coefficients have to be taken into
                    // account!) We encode this by demanding that
                    // (a-n)*(ASCDESC-1) = 0
                    // (so ASCDESC=0 is only OK for (a-n)=0).
                    final String dioAscDesc =
                        this.generateBool(nc, "ASCDESC_", coeffRanges);
                    SimplePolynomial polAscDesc =
                        SimplePolynomial.create(dioAscDesc);
                    mapAsc.put(i, polAscDesc);
                    mapDesc.put(i, polAscDesc);

                    polAscDesc = polAscDesc.minus(SimplePolynomial.ONE);
                    if (Globals.useAssertions) {
                        // otherwise we do not have the required interpretation
                        // form
                        assert (dioSet.size() == 1);
                    }
                    SimplePolynomial polAN = dioSet.iterator().next();
                    polAN = polAN.minus(this.minPol);
                    final Diophantine ascDesc = Diophantine.create(
                            polAN.times(polAscDesc),
                            ConstraintType.EQ);
                    dioCollection.add(ascDesc);
                } else if (dioSet.size() == 1) {
                    // if there only is one coefficient depending on x (e.g. in
                    // the linear case) then we do not introduce the helper
                    // variables ASC and DESC but directly return "a-n" and
                    // "n-a" as ASC and DESC
                    final SimplePolynomial polDio = dioSet.iterator().next();
                    final SimplePolynomial polAsc = polDio.minus(this.minPol);
                    mapAsc.put(i, polAsc);
                    mapDesc.put(i, polAsc.negate());
                } else {
                    final String dioAsc = this.generateBool(nc, "ASC_", coeffRanges);
                    SimplePolynomial polAsc = SimplePolynomial.create(dioAsc);
                    final String dioDesc = this.generateBool(nc, "DESC_", coeffRanges);
                    SimplePolynomial polDesc = SimplePolynomial.create(dioDesc);
                    mapAsc.put(i, polAsc);
                    mapDesc.put(i, polDesc);
                    polAsc = polAsc.minus(SimplePolynomial.ONE);
                    polDesc = polDesc.minus(SimplePolynomial.ONE);
                    for (final SimplePolynomial polDio : dioSet) {
                        // the argument at position i is ascending/descending,
                        // if all DioVars in DioSet "comply"

                        // (a-n)(ASC-1) >= 0 AND (b-n)(ASC-1) >= 0 AND ...
                        // for all coefficients a,b for x (x, x^2, xy, ...).
                        // (n-a)(DESC-1)...
                        SimplePolynomial constraintAsc =
                            polDio.minus(this.minPol);
                        SimplePolynomial constraintDesc =
                            constraintAsc.negate();
                        constraintAsc = constraintAsc.times(polAsc);
                        constraintDesc = constraintDesc.times(polDesc);
                        final Diophantine asc = Diophantine.create(constraintAsc,
                                    ConstraintType.GE);
                        final Diophantine desc = Diophantine.create(constraintDesc,
                                    ConstraintType.GE);
                        dioCollection.add(asc);
                        dioCollection.add(desc);
                    }
                }
            }
        }
    }

    /**
     * Generate constraints for all usable rules.
     * For every rule the corresponding active conditions are used to find out
     * which positions of (tuple?) function symbols are relevant for the rule's
     * interpretation. In the first step a fresh variable denoting "this rule
     * must be oriented l >= r" (and ... r >= l) is defined. To do that the
     * information "is this position ascending?" stored in positionIsAsc is used
     * for the relevant positions mentioned in the active condition. After
     * defining the orientation of the rule the constraints are generated
     * (dependent on the constraint generated just before).
     * @param active The map containg information about active arguments.
     * @param dioCollection The collection where all diophantine constraints
     * are collected.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param positionIsAsc Store SPs that denote a specific position is
     * ascending.
     * @param positionIsDesc Store SPs that denote a specific position is
     * descending.
     * @param coefficientMap Collect the DioVars that are coefficients of
     * non-tuple function symbols.
     */
    private void generateUsableRules(
            final Coeff nc,
            final Map<Rule, QActiveCondition> active,
            final Collection<Diophantine> dioCollection,
            final Map<String, BigInteger> coeffRanges,
            final Interpretation interpretation,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                positionIsAsc,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                positionIsDesc,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                coefficientMap,
            final Abortion aborter) throws AbortionException {
        for (final Map.Entry<Rule, QActiveCondition> entry : active.entrySet()) {
            final Rule rule = entry.getKey();
            final QActiveCondition condition = entry.getValue();

            // Enforce "l -r >= 0" when for (at least) one alternative in active
            // all mentioned coefficients of non-tuple function symbols are >= 0
            // and at least one mentioned coefficient (x, xy, x^2, ...) for
            // the tuple-symbol in that alternative is >= 0.

            // for each alternative build constraints meaning:
            // if the tuple-symbol position is ascending and all non-tuple
            // positions are >= 0 then set the rule is in U^1.

            // ruleCaseOne is a new polynomial that will be defined using side
            // constraints created in "generateConditionAscendingDescending".
            // If ruleCaseOne is not 0 then the rule must be oriented l >= r.

            final SimplePolynomial ruleCaseOne = SimplePolynomial.create(
                    this.generateBool(nc, "ASC_", coeffRanges));
            final SimplePolynomial ruleCaseMinusOne = SimplePolynomial.create(
                    this.generateBool(nc, "DESC_", coeffRanges));

            for (final Set<Pair<FunctionSymbol, Integer>> alternative
                    : condition.getSetRepresentation()) {
                this.generateConditionAscendingDescending(ruleCaseOne,
                        ruleCaseMinusOne, alternative, dioCollection,
                        positionIsAsc, positionIsDesc, coefficientMap);
            }

            final VarPolynomial constraint =
                interpretation.interpretTerm(rule.getLeft(), aborter).minus(
                        interpretation.interpretTerm(rule.getRight(), aborter));

            // generate constraints for the rule if it should be
            // ascending/descending
            this.generateUsableRule(ruleCaseOne, constraint, dioCollection);
            this.generateUsableRule(ruleCaseMinusOne, constraint.negate(),
                    dioCollection);
        }
    }

    /**
     * Add constraints to dioCollection that enforce some rules to be
     * "l - r >= 0" under a certain condition.
     * This is the case when all coefficients for this (usable) rule are
     * positive.
     * @param ruleHasToBeConsidered A simple polynomial with values in
     * [0 = NO, 1=YES] denoting that the constraint leftMinusRight has to be
     * >= 0.
     * @param leftMinusRight the difference of left-and right of the rule
     * @param dioCollection The collection where all diophantine constraints are
     * collected.
     */
    private void generateUsableRule(
            final SimplePolynomial ruleHasToBeConsidered,
            final VarPolynomial leftMinusRight,
            final Collection<Diophantine> dioCollection) {

        for (final SimplePolynomial coeff : leftMinusRight.getAllCoefficients()) {
            final SimplePolynomial newConstraint = ruleHasToBeConsidered.times(coeff);
            final Diophantine dio =
                Diophantine.create(newConstraint, ConstraintType.GE);
            dioCollection.add(dio);
        }
    }


    /**
     * Generate a DioVar that is 1 iff, based on the information for
     * the given alternative, the position of the tuple symbol is marked as
     * ascending and all others are >= 0.
     * @param ruleCaseOne The DioVar denoting that the corresponding rule
     * should be oriented "l <= r"
     * @param ruleCaseMinusOne The DioVar denoting that the corresponding rule
     * should be oriented "r <= l"
     * @param alternative A set containing all positions that have to be
     * ascending, if this alternative is chosen.
     * @param dioCollection The collection where all diophantine constraints
     * are collected.
     * @param positionIsAsc Store SPs that denote a specific position is
     * descending.
     * @param positionIsDesc Store SPs that denote a specific position is
     * ascending.
     * @param coefficientMap Collect the DioVars that are coefficients of
     * non-tuple function symbols.
     */
    private void generateConditionAscendingDescending(
            final SimplePolynomial ruleCaseOne,
            final SimplePolynomial ruleCaseMinusOne,
            final Set<Pair<FunctionSymbol, Integer>> alternative,
            final Collection<Diophantine> dioCollection,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                positionIsAsc,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                positionIsDesc,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                coefficientMap) {
        // "one" is the constraint that forces the rule to be in U^1.
        // ruleCaseOne is the "variable" that must be defined in this method:
        // If the positions mentioned in the (active condition) alternative
        // (which is a conjunction) all are ascending, then ruleCaseOne must be
        // set to some non-zero value. The constraint created to define
        // ruleCaseOne is called "one".

        SimplePolynomial one = ruleCaseOne.minus(SimplePolynomial.ONE);
        SimplePolynomial minusOne =
            ruleCaseMinusOne.minus(SimplePolynomial.ONE);

        boolean gotTuple = false;

        for (final Pair<FunctionSymbol, Integer> pair : alternative) {
            final FunctionSymbol f = pair.x;
            final int i = pair.y;

            if (positionIsAsc.containsKey(f)) {
                if (gotTuple) {
                    throw new RuntimeException("More than one tuple-symbol in "
                            + "conjunct of active constraint!");
                }

                gotTuple = true;
                // f is a tuple symbol, so take extra care
                final SimplePolynomial posIsAsc = positionIsAsc.get(f).get(i);
                final SimplePolynomial posIsDesc = positionIsDesc.get(f).get(i);
                one = one.times(posIsAsc);
                minusOne = minusOne.times(posIsDesc);
            } else {
                final SimplePolynomial coeff = coefficientMap.get(f).get(i);
                one = one.times(coeff);
                minusOne = minusOne.times(coeff);
            }
        }
        final Diophantine dioOne = Diophantine.create(one, ConstraintType.GE);
        dioCollection.add(dioOne);

        // if we got no tuple-symbol in given alternative then we can only have
        // normal usable rules, no reversed usable rules
        if (gotTuple) {
            final Diophantine dioMinusOne =
                Diophantine.create(minusOne, ConstraintType.GE);
            dioCollection.add(dioMinusOne);
        }
    }

    /**
     * Add an abstract interpretation for the given function symbol.
     * @param funcSym The function symbol to be interpreted.
     * @param isTuple denotes wheter funcSym is a tuple symbol.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param coefficientTupleMap Collect the DioVars that are part of the
     * coefficients of tuple function symbols.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param coefficientMap Collect the DioVars that are coefficients of
     * non-tuple function symbols.
     * @param dioCollection The collection where all diophantine constraints
     * are collected.
     * @param nonNegative Information about tuple symbols that have no
     * negative coefficient.
     */
    private void addInterpretation(
            final Coeff nc,
            final FunctionSymbol funcSym,
            final boolean isTuple,
            final Map<String, BigInteger> coeffRanges,
            final Interpretation interpretation,
            final Map<FunctionSymbol, Map<Integer, Set<SimplePolynomial>>>
                coefficientTupleMap,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                coefficientMap,
            final Collection<Diophantine> dioCollection,
            final Map<FunctionSymbol, SimplePolynomial> nonNegative
            ) {
        final VarPolynomial varPoly = interpretation.get(funcSym);
        if (varPoly == null) {
            if (isTuple) {
                final Map<Integer, Set<SimplePolynomial>> map =
                    new LinkedHashMap<Integer, Set<SimplePolynomial>>();
                for (int i = 0; i < funcSym.getArity(); i++) {
                    final Set<SimplePolynomial> set =
                        new LinkedHashSet<SimplePolynomial>();
                    map.put(i, set);
                }
                coefficientTupleMap.put(funcSym, map);
                this.addTupleInterpretation(nc, funcSym, coeffRanges, interpretation,
                        coefficientTupleMap, dioCollection, nonNegative);
            } else {
                final Map<Integer, SimplePolynomial> map =
                    new LinkedHashMap<Integer, SimplePolynomial>();
                coefficientMap.put(funcSym, map);
                this.addFunctionSymbolInterpretation(nc, funcSym, coeffRanges,
                        interpretation, coefficientMap);
            }
        }
    }

    /**
     * For tuple symbols (like FOO) the coefficients for variables
     * (so not x^2) may be negative. Introduce coefficients of the form
     * (a-n) where n is the minimal value (typically 1) and n ranges from 0 to
     * some positive value. This way the coefficient can be negative, zero or
     * positive depending on a.
     * The degree -2 is a special form where
     * Pol(FOO(x,..,z)) = ((a-n)x + ... + (b-n)z)^2 + (c-n).
     * For degree -2 all (standard) DPs are automatically bounded!
     * @param funcSym the tuple symbol that should be interpreted.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param coefficientTupleMap Collect the DioVars that are part of the
     * coefficients of tuple function symbols.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param dioCollection The collection where all diophantine constraints
     * are collected.
     * @param nonNegativeMap Information about tuple symbols that have no
     * negative coefficient.
     */
    private void addTupleInterpretation(
            final Coeff nc,
            final FunctionSymbol funcSym,
            final Map<String, BigInteger> coeffRanges,
            final Interpretation interpretation,
            final Map<FunctionSymbol, Map<Integer, Set<SimplePolynomial>>>
                coefficientTupleMap,
            final Collection<Diophantine> dioCollection,
            final Map<FunctionSymbol, SimplePolynomial> nonNegativeMap
            ) {
        if (Globals.useAssertions) {
            final int degreeMinusTwo = -2;
            assert (this.degreeTuple == degreeMinusTwo
                    || (this.degreeTuple > 0 && this.degreeTuple <= 2));
        }
        final int arity = funcSym.getArity();
        final VarPolynomial[] variables = new VarPolynomial[arity];
        VarPolynomial p = VarPolynomial.create(0);

        // add (a-n)x for all variables x

        Set<SimplePolynomial> allNonNegative = null;
        if (this.detectNonNegative) {
            allNonNegative = new LinkedHashSet<SimplePolynomial>(arity);
        }

        for (int i = 0; i < arity; i++) {
            final String pos = "POS_" + nc.getNext();
            SimplePolynomial posPol = SimplePolynomial.create(pos);
            if (arity <= 1) {
                coeffRanges.put(pos, this.maxPosForSmall);
            } else {
                coeffRanges.put(pos, this.maxPos);
            }

            coefficientTupleMap.get(funcSym).get(i).add(posPol);

            posPol = posPol.minus(this.minPol);

            if (this.detectNonNegative) {
                allNonNegative.add(posPol);
            }

            final VarPolynomial var =
                VarPolynomial.createVariable("x_" + (i + 1));
            variables[i] = var;
            final VarPolynomial addend = var.times(posPol);
            p = p.plus(addend);
        }

        if (this.detectNonNegative) {
            final String dioString = this.generateBool(nc, "NONNEGATIVE_", coeffRanges);
            final SimplePolynomial dioVar = SimplePolynomial.create(dioString);
            nonNegativeMap.put(funcSym, dioVar);
            for (final SimplePolynomial poly : allNonNegative) {
                final Diophantine dio =
                    Diophantine.create(poly.times(dioVar), ConstraintType.GE);
                dioCollection.add(dio);
            }
        }

        final int degreeMinusTwo = -2;
        if (this.degreeTuple == degreeMinusTwo) {
            p = p.times(p);
        } else if (this.degreeTuple == 2) {
            // add (a-n)x^2 and (a-n)xy for all variables x,y,..
            // position of first included variable
            for (int j = 0; j < arity; j++) {
                // start of remaining variables
                for (int k = j; k < arity; k++) {
                    // now collect the variables
                    final String pos = "POS_" + nc.getNext();
                    if (arity <= 1) {
                        coeffRanges.put(pos, this.maxPosForSmall);
                    } else {
                        coeffRanges.put(pos, this.maxPos);
                    }
                    // Remember for the positions j and l that POS_
                    // is used for these. This information will be used to
                    // decide whether the position j or l is ascending/...
                    SimplePolynomial coeffPol =
                        SimplePolynomial.create(pos);
                    coefficientTupleMap.get(funcSym).get(j).add(coeffPol);
                    coefficientTupleMap.get(funcSym).get(k).add(coeffPol);
                    coeffPol = coeffPol.minus(this.minPol);
                    VarPolynomial addend = VarPolynomial.create(coeffPol);
                    addend = addend.times(variables[j]);
                    addend = addend.times(variables[k]);
                    p = p.plus(addend);
                }
            }
        }

        // add constant part
        final String pos = "POS_" + nc.getNext();
        if (arity <= 1) {
            coeffRanges.put(pos, this.maxPosForSmall);
        } else {
            coeffRanges.put(pos, this.maxPos);
        }
        SimplePolynomial coeff =
            SimplePolynomial.create(pos);
        coeff = coeff.minus(this.minPol);
        final VarPolynomial addend = VarPolynomial.create(coeff);
        p = p.plus(addend);

        interpretation.extend(funcSym, p);
    }

    /**
     * For normal function symbols all coefficients may not be negative.
     * @param funcSym the function symbol that should be interpreted.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param coefficientMap Collect the DioVars that are coefficients of
     * non-tuple function symbols.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     */
    private void addFunctionSymbolInterpretation(
            final Coeff nc,
            final FunctionSymbol funcSym,
            final Map<String, BigInteger> coeffRanges,
            final Interpretation interpretation,
            final Map<FunctionSymbol, Map<Integer, SimplePolynomial>>
                coefficientMap) {
        final int arity = funcSym.getArity();
        final VarPolynomial[] variables = new VarPolynomial[arity];
        VarPolynomial p = VarPolynomial.create(0);

        // add a*x for all variables x
        for (int i = 0; i < arity; i++) {
            final String posDio = "POS_" + nc.getNext();
            final SimplePolynomial pos = SimplePolynomial.create(posDio);
            if (arity <= 1) {
                coeffRanges.put(posDio, this.maxForSmall);
            } else {
                coeffRanges.put(posDio, this.max);
            }
            coefficientMap.get(funcSym).put(i, pos);
            final VarPolynomial var =
                VarPolynomial.createVariable("x_" + (i + 1));
            variables[i] = var;
            final VarPolynomial addend = var.times(pos);
            p = p.plus(addend);
        }

        // add constant part
        final String constDio = "POS_" + nc.getNext();
        final SimplePolynomial coeff =
            SimplePolynomial.create(constDio);
        if (arity <= 1) {
            coeffRanges.put(constDio, this.maxForSmall);
        } else {
            coeffRanges.put(constDio, this.max);
        }
        final VarPolynomial addend = VarPolynomial.create(coeff);

        p = p.plus(addend);
        interpretation.extend(funcSym, p);
    }

    /**
     * Generate diophantine constraints that ensure each rule in the given
     * problem is in P_>, P_>= or P_bound.
     * @param problemMap A map with rules and their corresponding constraints
     * that have to be fulfilled.
     * @param dioCollection The collection where all diophantine constraints
     * are collected.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param strictRules Collect the constraints (value) that have to be
     * fulfilled such that the rule (map's key) is in P_>.
     * @param boundRules Collect the constraints (value) that have to be
     * fulfilled such that the rule (map's key) is in P_bound.
     * @param cTerms Collect the terms t that appear in "t >= c" for the fresh
     * function symbol c. Based on these terms c will be defined later.
     * @param boundedSymbols The set of function symbols of that we know that
     *   it is always bounded, i.e. if t = f(..) and f in boundedSymbols then
     *   Pol(t) is bounded. May be null.
     * @param nonNegativeMap Information about tuple symbols that have no
     * negative coefficient.
     */
    private void generateStrictNonStrictBound(
            final Coeff nc,
            final Map<Rule, List<Implication>> problemMap,
            final Collection<Diophantine> dioCollection,
            final Map<String, BigInteger> coeffRanges,
            final Interpretation interpretation,
            final Set<TRSTerm> cTerms,
            final Map<Rule, String> strictRules,
            final Map<Rule, String> boundRules,
            final Set<FunctionSymbol> boundedSymbols,
            final Map<FunctionSymbol, SimplePolynomial> nonNegativeMap,
            final Abortion aborter) throws AbortionException {

        final Map<Rule, Map<Constraint, String>> strictMap =
            new LinkedHashMap<Rule, Map<Constraint, String>>();
        final Map<Rule, Map<Constraint, String>> boundMap =
            new LinkedHashMap<Rule, Map<Constraint, String>>();

        SimplePolynomial countStrictRules = SimplePolynomial.ZERO;
        SimplePolynomial countBoundRules = SimplePolynomial.ZERO;

        for (final Map.Entry<Rule, List<Implication>> entry : problemMap.entrySet()) {
            final Rule rule = entry.getKey();
            final List<Implication> implicationList = entry.getValue();

            final Map<Constraint, String> ruleMapStrict =
                new LinkedHashMap<Constraint, String>();
            final Map<Constraint, String> ruleMapBound =
                new LinkedHashMap<Constraint, String>();

            strictMap.put(rule, ruleMapStrict);
            boundMap.put(rule, ruleMapBound);

            for (final Implication constraint : implicationList) {
                // generate DioVars that imply some constraint is solved
                this.generateFromConstraint(nc, constraint, constraint, ruleMapStrict,
                        ruleMapBound, dioCollection, coeffRanges,
                        interpretation, cTerms, boundedSymbols, nonNegativeMap, aborter);
            }

            // strict
            Collection<String> dios = ruleMapStrict.values();
            if (dios.size() == 1) {
                final String first = dios.iterator().next();
                strictRules.put(rule, first);
                countStrictRules =
                    countStrictRules.plus(SimplePolynomial.create(first));
            } else {
                // a rule is in P_> if _all_ generated constraints are
                // fulfilled.
                // a+b+c+d >= 4*X [example for four constraints a,b,c,d]
                // X = 1 => all constraints are fulfilled

                SimplePolynomial isStrict =
                    SimplePolynomial.create(-dios.size());
                final String dioString = this.generateBool(nc, "STRICTRULE_", coeffRanges);
                strictRules.put(rule, dioString);
                isStrict = isStrict.times(SimplePolynomial.create(dioString));
                for (final String dio : dios) {
                    isStrict = isStrict.plus(SimplePolynomial.create(dio));
                }
                final Diophantine isStrictDio =
                    Diophantine.create(isStrict, ConstraintType.GE);
                dioCollection.add(isStrictDio);

                countStrictRules =
                    countStrictRules.plus(SimplePolynomial.create(dioString));
            }

            // bound
            dios = ruleMapBound.values();
            if (dios.size() == 1) {
                final String first = dios.iterator().next();
                boundRules.put(rule, first);
                countBoundRules =
                    countBoundRules.plus(SimplePolynomial.create(first));
            } else {
                dios = boundMap.get(rule).values();
                SimplePolynomial isBound =
                    SimplePolynomial.create(-dios.size());
                final String dioString = this.generateBool(nc, "BOUNDRULE_", coeffRanges);
                boundRules.put(rule, dioString);
                isBound = isBound.times(SimplePolynomial.create(dioString));
                for (final String dio : dios) {
                    isBound = isBound.plus(SimplePolynomial.create(dio));
                }
                final Diophantine isBoundDio =
                    Diophantine.create(isBound, ConstraintType.GE);
                dioCollection.add(isBoundDio);
                countBoundRules =
                    countBoundRules.plus(SimplePolynomial.create(dioString));
            }
        }

        // one rule has to strict, one has to be bound
        final Diophantine oneStrict =
            Diophantine.create(countStrictRules, ConstraintType.GT);
        final Diophantine oneBound =
            Diophantine.create(countBoundRules, ConstraintType.GT);

        dioCollection.add(oneStrict);
        dioCollection.add(oneBound);
    }

    /**
     * Take a look at the given constraint and delegate the work.
     * @param constraint The current constraint.
     * @param originalConstraint The original constraint that can be used to get
     * a connection to the rule where it comes from.
     * @param strictMap The map containing all information about rules that may
     * be in P_>.
     * @param boundMap The map containing all information about rules that may
     * be in P_bound.
     * @param dioCollection The collection where all diophantine constraints are
     * collected.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param interpretation The abstract polynomial interpretation over
     * integers. The abstract polynomial interpretation over
     * integers.
     * @param cTerms Collect the terms t that appear in "t >= c" for the fresh
     * function symbol c. Based on these terms c will be defined later.
     * @param boundedSymbols The set of function symbols of that we know that
     *   it is always bounded, i.e. if t = f(..) and f in boundedSymbols then
     *   Pol(t) is bounded. May be null.
     * @param nonNegativeMap Information about tuple symbols that have no
     * negative coefficient.
     */
    private void generateFromConstraint(
            final Coeff nc,
            final Constraint constraint,
            final Constraint originalConstraint,
            final Map<Constraint, String> strictMap,
            final Map<Constraint, String> boundMap,
            final Collection<Diophantine> dioCollection,
            final Map<String, BigInteger> coeffRanges,
            final Interpretation interpretation,
            final Set<TRSTerm> cTerms,
            final Set<FunctionSymbol> boundedSymbols,
            final Map<FunctionSymbol, SimplePolynomial> nonNegativeMap,
            final Abortion aborter) throws AbortionException {
        if (constraint.isTermAtom()) {
            // An atomic constraint (l ~ r)
            final TermAtom atom = (TermAtom) constraint;
            this.generateFromAtomWrapper(nc, atom, originalConstraint, strictMap,
                        boundMap, dioCollection, coeffRanges,
                        interpretation, cTerms, boundedSymbols, nonNegativeMap, aborter);
       } else if (constraint.isImplication()) {
           final Implication implication = (Implication) constraint;
           if (implication.getConditions().isEmpty()) {
               this.generateFromConstraint(nc, implication.getConclusion(),
                       originalConstraint, strictMap, boundMap,
                       dioCollection, coeffRanges, interpretation, cTerms,
                       boundedSymbols, nonNegativeMap, aborter);
           } else {
               this.generateFromImplication(nc, implication, originalConstraint,
                       boundMap, dioCollection, coeffRanges, interpretation,
                       boundedSymbols, nonNegativeMap, aborter);
           }
       } else {
           if (Globals.useAssertions) {
               assert (false) : "What is that?";
           }
       }
    }

    /**
     * Handle implications.
     * @param implication The current constraint, which is an implication.
     * @param originalConstraint The original constraint that can be used to get
     * a connection to the rule where it comes from.
     * @param boundMap The map containing all information about rules that may
     * be in P_bound.
     * @param dioCollection The collection where all diophantine constraints are
     * collected.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param boundedSymbols The set of function symbols of that we know that
     * it is always bounded, i.e. if t = f(..) and f in boundedSymbols then
     * Pol(t) is bounded. May be null.
     * @param nonNegativeMap Information about tuple symbols that have no
     * negative coefficient.
     */
    private void generateFromImplication(
            final Coeff nc,
            final Implication implication,
            final Constraint originalConstraint,
            final Map<Constraint, String> boundMap,
            final Collection<Diophantine> dioCollection,
            final Map<String, BigInteger> coeffRanges,
            final Interpretation interpretation,
            final Set<FunctionSymbol> boundedSymbols,
            final Map<FunctionSymbol, SimplePolynomial> nonNegativeMap,
            final Abortion aborter) throws AbortionException {
        if (!implication.getQuantor().isEmpty()) {
            if (Globals.useAssertions) {
                assert (false) : "Why does this happen?";
            }
            return;
        }
        if (!implication.getConclusion().isTermAtom()) {
            if (Globals.useAssertions) {
                assert (false) : "Why does this happen?";
            }
            return;
        }
        final TermAtom conclusion = (TermAtom) implication.getConclusion();
        final TRSTerm leftTerm = conclusion.getLeft();
        // Take care of one condition (for all conditions).
        // Strict and nonstrict formulae are the same here
        // => hence as we have to satisfy all non-strict conditions
        //    we do not need the strictMap here.
        final VarPolynomial left =
            interpretation.interpretTerm(leftTerm, aborter);
        VarPolynomial leftMinusRight = left;
        leftMinusRight = leftMinusRight.minus(
                    interpretation.interpretTerm(conclusion.getRight(), aborter));

        SimplePolynomial sumBoundVars = SimplePolynomial.ZERO;
        SimplePolynomial sumNonStrictVars = SimplePolynomial.ZERO;
        final Collection<Constraint> conditions = implication.getConditions();

        final String boundVarGlobal = this.generateBool(nc, "BOUND_", coeffRanges);
        SimplePolynomial boundVarGlobalPol =
            SimplePolynomial.create(boundVarGlobal);
        boundMap.put(originalConstraint, boundVarGlobal);

        // special case for only one condition:
        // then we do not have to introduce all the
        // intermediate OneCondition... variables
        final boolean onlyOne = (conditions.size() == 1);
        final FunctionSymbol leftRootSymbol
            = ((TRSFunctionApplication) leftTerm).getRootSymbol();
        final boolean alwaysBounded = leftTerm.isVariable()
            || (boundedSymbols != null
                    && boundedSymbols.contains(leftRootSymbol));

        if (alwaysBounded) {
            // fix boundVarGlobal to be 1 to get less indeterminism!
            // encoded as (boundvar - 1 = 0)
            final Diophantine dioBound = Diophantine.create(boundVarGlobalPol.plus(
                    SimplePolynomial.MINUS_ONE), ConstraintType.EQ);
            dioCollection.add(dioBound);
        }

        SimplePolynomial nonNegativePol = null;
        if (this.detectNonNegative) {
            nonNegativePol = nonNegativeMap.get(leftRootSymbol);
        }

        if (this.detectNonNegative && nonNegativePol != null) {
            // force the bound variable to one if the nonnegative
            // variable is set.
            final SimplePolynomial setBound =
                boundVarGlobalPol.minus(nonNegativePol);
            final Diophantine setBoundDio =
                Diophantine.create(setBound, ConstraintType.GE);
            dioCollection.add(setBoundDio);
        }

        for (final Constraint condition : conditions) {
            if (!condition.isTermAtom()) {
                if (Globals.useAssertions) {
                    assert (false) : "Why does this happen?";
                }
                return;
            }
            SimplePolynomial nonStrictPol;
            SimplePolynomial boundPol = null;
            if (onlyOne) {
                nonStrictPol = null;
                if (!alwaysBounded) {
                    boundPol = boundVarGlobalPol;
                }
            } else {
                final String nonStrictVar =
                    this.generateBool(nc, "OneConditionNonStrict_", coeffRanges);
                nonStrictPol = SimplePolynomial.create(nonStrictVar);
                sumNonStrictVars = sumNonStrictVars.plus(nonStrictPol);

                if (!alwaysBounded) {
                    final String boundVar =
                        this.generateBool(nc, "OneConditionBound_", coeffRanges);
                    boundPol = SimplePolynomial.create(boundVar);
                    sumBoundVars = sumBoundVars.plus(boundPol);
                }
            }

            final TermAtom atom = (TermAtom) condition;

            final TRSTerm leftSide = atom.getLeft();
            final TRSTerm rightSide = atom.getRight();
            VarPolynomial nonStrict = interpretation.interpretTerm(leftSide, aborter);
            final VarPolynomial bound = alwaysBounded ? null : left.minus(nonStrict);
            nonStrict = nonStrict.minus(
                        interpretation.interpretTerm(rightSide, aborter));
            nonStrict = leftMinusRight.minus(nonStrict);

            for (final SimplePolynomial coeff : nonStrict.getAllCoefficients()) {
                SimplePolynomial constraintNonStrict = coeff;
                if (!onlyOne) {
                    constraintNonStrict =
                        constraintNonStrict.times(nonStrictPol);
                }
                final Diophantine dioNonStrict =
                    Diophantine.create(constraintNonStrict, ConstraintType.GE);
                dioCollection.add(dioNonStrict);
            }

            if (!alwaysBounded) {
                for (final SimplePolynomial coeff : bound.getAllCoefficients()) {
                    SimplePolynomial constraintBound =
                        coeff.times(boundPol);
                    if (this.detectNonNegative && nonNegativePol != null) {
                        // if the nonnegative variable is set for the function
                        // symbol of the conclusion then the check for
                        // boundedness may be skipped.
                        final SimplePolynomial nonNegative =
                            SimplePolynomial.ONE.minus(nonNegativePol);
                        constraintBound = constraintBound.times(nonNegative);
                    }
                    final Diophantine dioBound =
                        Diophantine.create(constraintBound, ConstraintType.GE);
                    dioCollection.add(dioBound);
                }
            }
        }

        if (!onlyOne) {
            // If we did not have only one constraint then
            // enforce that at for at least one condition
            // of the formula is fulfilled.

            final Diophantine dioNonStrict =
                Diophantine.create(sumNonStrictVars, ConstraintType.GT);
            dioCollection.add(dioNonStrict);

            // In the case where (a+b+c) is 0, so no part is bound,
            // and if X = 1 denotes at least one is bound then the formula
            // must be satisfiable if X is false (=0).
            // Otherwise (only) when (a+b+c) > 0 then X may be chosen to be 1.
            // (a+b+c) - X >= 0 does the trick.
            if (!alwaysBounded) {
                // if the nonnegative variable for the function symbol of the
                // conclusion is set, then this can be skipped.
                if (this.detectNonNegative && nonNegativePol != null) {
                    final SimplePolynomial nonNegative =
                        SimplePolynomial.ONE.minus(nonNegativePol);
                    boundVarGlobalPol = boundVarGlobalPol.times(nonNegative);
                }
                sumBoundVars = sumBoundVars.minus(boundVarGlobalPol);

                final Diophantine dioBound =
                    Diophantine.create(sumBoundVars, ConstraintType.GE);
                dioCollection.add(dioBound);
            }
        }

    }

    /**
     * This methods generates constraints for a given atom.
     * The DioVars (in the triple dioVars) can only be set to 1 if the
     * atom can be aligned using ">", ">=" or "bound" (correspondingly).
     * By using these DioVars outside of this method it is possible to have
     * several alternative possible solutions, where this atom may not be
     * aligned using ">".
     * The simple case is used in generateFromAtom, where the constraints for
     * the given atom have to be fulfilled without alternative.
     * @param atom The current constraint, which is an atom.
     * @param dioVars Two DioVars denoting that the atom can be oriented
     * strict/bound.
     * @param dioCollection The collection where all diophantine constraints are
     * collected.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param cTerms Collect the terms t that appear in "t >= c" for the fresh
     * function symbol c. Based on these terms c will be defined later.
     * @param boundedSymbols The set of function symbols of that we know that
     *   it is always bounded, i.e. if t = f(..) and f in boundedSymbols then
     *   Pol(t) is bounded. May be null.
     * @param nonNegativeMap Information about tuple symbols that have no
     * negative coefficient.
     */
    private void generateFromAtom(
            final TermAtom atom,
            final Pair<String, String> dioVars,
            final Collection<Diophantine> dioCollection,
            final Interpretation interpretation,
            final Set<TRSTerm> cTerms,
            final Set<FunctionSymbol> boundedSymbols,
            final Map<FunctionSymbol, SimplePolynomial> nonNegativeMap,
            final Abortion aborter) throws AbortionException {
        final TRSTerm left = atom.getLeft();
        final TRSTerm right = atom.getRight();

        final VarPolynomial polLeft = interpretation.interpretTerm(left, aborter);
        final VarPolynomial polRight = interpretation.interpretTerm(right, aborter);
        final VarPolynomial leftMinusRight = polLeft.minus(polRight);

        final SimplePolynomial strictVarPol =
            SimplePolynomial.create(dioVars.x);
        final SimplePolynomial boundVarPol = SimplePolynomial.create(dioVars.y);

        // strict and non-strict

        for (final SimplePolynomial coeff
                : leftMinusRight.getCoefficientsOfVariables()) {
            final Diophantine dioPartialDerivations =
                Diophantine.create(coeff, ConstraintType.GE);
            dioCollection.add(dioPartialDerivations);
        }
        // Approach 1)
        // Note that from the non-strict requirement we know that
        // constant >= 0.
        //
        // Hence for the strict requirement we just have to encode
        // constant - strictVarPol >= 0:
        // If strictVarPol is 0 then this constraint is satisfiable
        // and (only) if constant > 0 then strictVarPol can be chosen
        // to be 1!
        // Alternative encodings which may be faster for SAT:
        //   2) (constant - strictVarPol) * strictVarPol >= 0
        //    SimplePolynomial constantStrictX =
        //        constant.minus(strictVarPol);
        //    constantStrictX = constantStrictX.times(strictVarPol);
        //
        //    Diophantine dioConstStrictX =
        //        Diophantine.create(constantStrictX, ConstraintType.GE);
        //
        //    dioCollection.add(dioConstStrictX);
        //   3) constant * strictVarPol + (1 - strictVarPol) > 0
        //    SimplePolynomial constantStrictY =
        //        constant.times(strictVarPol);
        //    SimplePolynomial mayBe =
        //        SimplePolynomial.ONE.minus(strictVarPol);
        //    constantStrictY = constantStrictY.plus(mayBe);
        //    Diophantine dioConstStrictY =
        //        Diophantine.create(constantStrictY, ConstraintType.GT);
        //    dioCollection.add(dioConstStrictY);
        // 2) and 3) are longer and more complex but they are also satisfiable
        // without the knowledge that constant >= 0,and hence, they are
        // "more easy" to satisfy. A small benchmark showed that approach 1 is
        // best: 33.9 / 35.2 / 38.4 seconds for all examples.

        final SimplePolynomial constant = leftMinusRight.getConstantPart();
        final Diophantine dioConstNonStrict =
            Diophantine.create(constant, ConstraintType.GE);
        dioCollection.add(dioConstNonStrict);

        final SimplePolynomial constantStrict =
            constant.minus(strictVarPol);

        final Diophantine dioConstStrict =
            Diophantine.create(constantStrict, ConstraintType.GE);
        dioCollection.add(dioConstStrict);

        // bound
        cTerms.add(left);
        if (!left.isVariable()) {
            // a variable is always bound as it is instantiated by positive
            // values
            final FunctionSymbol leftRootSymbol =
                ((TRSFunctionApplication) left).getRootSymbol();
            if (boundedSymbols == null
                    || !boundedSymbols.contains(leftRootSymbol)) {
                SimplePolynomial nonNegativePol = null;
                if (this.detectNonNegative) {
                    nonNegativePol = nonNegativeMap.get(leftRootSymbol);
                }

                if (this.detectNonNegative && nonNegativePol != null) {
                    // force the bound variable to one if the nonnegative
                    // variable is set.
                    final SimplePolynomial setBound =
                        boundVarPol.minus(nonNegativePol);
                    final Diophantine setBoundDio =
                        Diophantine.create(setBound, ConstraintType.GE);
                    dioCollection.add(setBoundDio);
                }

                for (final SimplePolynomial coeff
                        : polLeft.getCoefficientsOfVariables()) {
                    SimplePolynomial bound = coeff.times(boundVarPol);

                    if (this.detectNonNegative && nonNegativePol != null) {
                        // if the nonnegative variable is set the check for
                        // boundedness can be skipped.
                        final SimplePolynomial nonNegative =
                            SimplePolynomial.ONE.minus(nonNegativePol);
                        bound = bound.times(nonNegative);
                    }

                    final Diophantine dioBound =
                        Diophantine.create(bound, ConstraintType.GE);
                    dioCollection.add(dioBound);

                }
            }
        }
    }

    /**
     * This method calls generateFromAtom, which only generates constraints that
     * have to be fulfilled if some prefix (DioVar(s)) is 1.
     * @param atom The current constraint, which is an atom.
     * @param originalConstraint The original constraint that can be used to get
     * a connection to the rule where it comes from.
     * @param strictMap The map containing all information about rules that may
     * be in P_>.
     * @param boundMap The map containing all information about rules that may
     * be in P_bound.
     * @param dioCollection The collection where all diophantine constraints are
     * collected.
     * @param coeffRanges The map storing information about the possible values
     * for the DioVars.
     * @param interpretation The abstract polynomial interpretation over
     * integers.
     * @param cTerms Collect the terms t that appear in "t >= c" for the fresh
     * function symbol c. Based on these terms c will be defined later.
     * @param boundedSymbols The set of function symbols of that we know that
     *   it is always bounded, i.e. if t = f(..) and f in boundedSymbols then
     *   Pol(t) is bounded. May be null.
     * @param nonNegativeMap Information about tuple symbols that have no
     * negative coefficient.
     */
    private void generateFromAtomWrapper(
            final Coeff nc,
            final TermAtom atom,
            final Constraint originalConstraint,
            final Map<Constraint, String> strictMap,
            final Map<Constraint, String> boundMap,
            final Collection<Diophantine> dioCollection,
            final Map<String, BigInteger> coeffRanges,
            final Interpretation interpretation,
            final Set<TRSTerm> cTerms,
            final Set<FunctionSymbol> boundedSymbols,
            final Map<FunctionSymbol, SimplePolynomial> nonNegativeMap,
            final Abortion aborter) throws AbortionException {
        final String strictVar = this.generateBool(nc, "STRICT_", coeffRanges);
        final String boundVar = this.generateBool(nc, "BOUND_", coeffRanges);

        final Pair<String, String> dioVars =
            new Pair<String, String>(strictVar, boundVar);

        this.generateFromAtom(atom, dioVars, dioCollection, interpretation, cTerms,
                boundedSymbols, nonNegativeMap, aborter);

        strictMap.put(originalConstraint, strictVar);
        boundMap.put(originalConstraint, boundVar);
    }

    private static class Coeff {
        int nextCoeff = 0;

        public int getNext() {
            return ++this.nextCoeff;
        }
    }

    /**
     * The proof for this processor.
     * @author cotto
     */
    private static class NonInfProof extends QDPProof {

        /**
         * The interpretation without diophantine variables.
         */
        private final Interpretation inter;

        /**
         * The P rules in the QDPProblem that are strict.
         */
        private final Set<Rule> strict;

        /**
         * The P rules in the QDPProblem that are bound.
         */
        private final Set<Rule> bound;

        /**
         * The usable rules that have been oriented.
         */
        private final Map<Rule, QActiveCondition.Direction> usableRules;

        /**
         * The proof giving information about the induction steps.
         */
        private final InductionCalculusProof icProof;

        /**
         * The input DP-problem
         */
        private final QDPProblem origQDP;

        /**
         * The output DP-problems
         */
        private final List<QDPProblem> resultingQDPs;


        /**

         * @param boundPRules The P rules that are bound.
         * @param strictPRules  The P rules that are strict.
         * @param interpretation The interpretation (without DioVars).
         * @param icProofParam The proof giving information about the induction
         * steps.
         * where one has to be in P_> and all others in P_\geq, at least one has
         * @param usableRulesParam Information about the usable rules, including
         * direction.
         * to be in P_bound.
         * @param origQDP the input DP problem
         */
        public NonInfProof(
                final Interpretation interpretation,
                final Set<Rule> strictPRules,
                final Set<Rule> boundPRules,
                final Map<Rule, QActiveCondition.Direction> usableRulesParam,
            final InductionCalculusProof icProofParam,
            final QDPProblem origQDP,
            final List<QDPProblem> resultingQDPs)
        {
            super();
            this.inter = interpretation;
            this.strict = strictPRules;
            this.bound = boundPRules;
            this.usableRules = usableRulesParam;
            this.icProof = icProofParam;
            this.origQDP = origQDP;
            this.resultingQDPs = resultingQDPs;
        }

        /**
         * Generate the string representing the proof.
         * @param o The export util for special symbols.
         * @param level The verbosity level.
         * @return The proof as a string.
         */
        @Override
        public String export(final Export_Util o,
                final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("The DP Problem is simplified using the Induction "
                    + "Calculus "+o.cite(Citation.NONINF)+" with the following steps:");
            sb.append(o.newline());
            sb.append(this.icProof.export(o));

            sb.append(o.newline());

            /*
            sb.append("The following constraints are handled.");
            sb.append(o.newline());
            for (Map.Entry<Rule, List<Implication>> entry
                    : this.problemMap.entrySet()) {
                if (entry.getValue().size() > 0) {
                    sb.append("For DP ");
                    sb.append(entry.getKey().export(o));
                    sb.append(":");
                    sb.append(o.newline());
                    sb.append(o.set(entry.getValue(), Export_Util.ITEMIZE));
                }
            } */
            sb.append("Using the following integer polynomial ordering the "
                    + " resulting constraints can be solved ");
            sb.append(o.newline());
            sb.append(o.export(this.inter));
            sb.append(o.newline());
            sb.append("The following pairs "
                    + " are in P" + o.sub(o.gtSign()) + ":");
            sb.append(o.set(this.strict, Export_Util.RULES));
            sb.append("The following pairs are in P" + o.sub("bound") + ":");
            sb.append(o.set(this.bound, Export_Util.RULES));
            if (this.usableRules.isEmpty()) {
                sb.append("There are no usable rules");
            } else {
                sb.append("The following rules are usable:");
                final List<String> usables =
                    new ArrayList<String>(this.usableRules.size());
                for (final Map.Entry<Rule, Direction> usable
                        : this.usableRules.entrySet()) {
                    final Rule rule = usable.getKey();
                    final Direction dir = usable.getValue();
                    TRSTerm left, right;
                    if (dir == Direction.Reversed) {
                        left = rule.getRight();
                        right = rule.getLeft();
                    } else {
                        left = rule.getLeft();
                        right = rule.getRight();
                    }
                    final String s = left.export(o) + " " + (dir == Direction.Both
                            ? o.leftrightarrow() : o.rightarrow())
                      + " " + right.export(o);
                    usables.add(s);
                }
                sb.append(o.set(usables, Export_Util.RULES));
            }
            return sb.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (modus.isPositive()) {
                final Element condRedPair =
                    this.icProof.toCPF(doc, xmlMetaData, this.strict, this.bound, this.origQDP.getP());
                final Element prf = CPFTag.GENERAL_RED_PAIR_PROC.create(doc);
                prf.appendChild(this.inter.toCPF(doc, xmlMetaData));
                prf.appendChild(CPFTag.STRICT.create(doc, CPFTag.rules(doc, xmlMetaData, this.strict)));
                prf.appendChild(CPFTag.BOUND.create(doc, CPFTag.rules(doc, xmlMetaData, this.bound)));
                prf.appendChild(condRedPair);
                for (final Element child : childrenProofs) {
                    prf.appendChild(child);
                }
                return CPFTag.DP_PROOF.create(doc, prf);
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultingQDPs.get(modus.negativeReason()));
            }
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }

    public static class Arguments {

        /**
         * The degree used to interpret tuple symbols.
         * 1)  F(x,y) = a*x + b*y + c
         * 2)  F(x,y) = a*x + b*y + c*xy + d*x^2 + e*y^2 + f
         * -2) F(x,y) = (a*x + b*y)^2 + c
         */
        public int degreeTuple;

        /**
         * if true then some checks for boundedness may be skipped for tuple
         * symbols without negative interpretation.
         */
        public boolean detectNonNegative;

        /**
         * Enforce that at least one position will be interpreted with a
         * negative coefficient.
         */
        public boolean enforceNegative;

        /**
         * The (SAT) engine used to construct the resulting formula.
         */
        public Engine engine;

        /**
         * Limit the number of possible induction steps.
         */
        public int inductionCounter;

        /**
         * The length of the chain in left direction.
         */
        public int leftChainCounter;

        /**
         * The maximum value used for coefficients that may not be negative.
         * For max=2 these coefficients can take values 0,1,2.
         * For tuple symbols (which may have negative coefficients) the value for
         * maxPos is adapted, so that the max number (2 in the example) can be
         * reached even though the minimum is subtracted from the coefficient.
         * For max=2 and min=1 (so (a-1) is a coefficient for a position of a tuple
         * symbol) this will calculate maxPos as 2+1, so that (a-1) can be
         * -1,0,1,2.
         */
        public int maximum;

        /**
         * The maximum value used for coefficients that may not be negative, but
         * limited for function symbols with arity 1 or 0.
         * For maxForSmall=2 these coefficients can take values 0,1,2.
         * For tuple symbols (which may have negative coefficients) the value for
         * maxPosForSmall is adapted, so that the maxForSmall number (2 in the
         * example) can be reached even though the minimum is subtracted from the
         * coefficient.
         * For maxForSmall=2 and min=1 (so (a-1) is a coefficient for a position
         * of a tuple symbol) this will calculate maxPosForSmall as 2+1, so that
         * (a-1) can be -1,0,1,2.
         */
        public int maximumForSmall;

        /**
         * The lowest possible coefficient (times -1). This should be >0 to make
         * this processor useful. A value of 2 means that -2*x is possible as part
         * of the interpretation.
         * (See setMaximum).
         */
        public int minimum;

        /**
         * The length of the chain in right direction.
         */
        public int rightChainCounter;
        public DiophantineSATConverter satConverter;
    }

}

