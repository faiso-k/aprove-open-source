package aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Finding non-monotonic Polynomial Orders with max (and min, maybe)
 * for the non-monotonic reduction pair processor.
 *
 * Based on version 1.83 of the corresponding paper, which should not
 * be all that different from the final version in the proceedings of
 * RTA'08.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class NonMonPoloInterpretation {

    // true:  use nu-RL
    // false: use nu-LN
    private static final boolean RIGHT_LINEAR_SUFFICES = false;

    // Apply a substitution [everything / x] on the term for i(t, p)
    // and d(t, p)? May improve caching, but consumes some time.
    private static final boolean JUST_ONE_VAR = false;

    // Also include the encoding of part b) of the Thm?
    // Increases power, but also search space size.
    private static final boolean encodeB = true;

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo.NonMonPoloInterpretation");

    private static final Citation[] citations = {Citation.POLO, Citation.NEGPOLO, Citation.MAXPOLO};

    private static final String COEFF_PREFIX = "a_";
    private static final String SEARCHSTRICT_PREFIX = "s_";

    // the following two constants must be distinct, and
    // not one of them may be a prefix of the other.
    public static final String VAR_PREFIX = TRSTerm.STANDARD_PREFIX + "_";
    public static final String HOOK_PREFIX = TRSTerm.SECOND_STANDARD_PREFIX + "_";

    private final Map<FunctionSymbol, OpVarPolynomial> interpretation; // the interpretation

    // For each function symbol f, there are two
    // propositional variables us_f and \overline{us}_f. These are stored here.
    // Access via method getFURDirection(FunctionSymbol).
    private final Map<FunctionSymbol, Pair<Formula<Diophantine>, Formula<Diophantine>>> fURDirection;

    // For each function symbol f and index i of f, there are two
    // propositional variables ic_{f,i} and dc_{f,i}. These are stored here.
    // Access via method getIncDec(FunctionSymbol).
    private final Map<FunctionSymbol, Pair<Formula<Diophantine>[], Formula<Diophantine>[]>> fIncDec;

    // For terms t and positions q, there are two
    // formulae ic_{t,q} and dc_{t,q}. These are stored here.
    // Access via methods ic(t,q) and dc(t,q).
    private final Map<TRSTerm, Map<Position, Formula<Diophantine>>> ic_t_q;
    private final Map<TRSTerm, Map<Position, Formula<Diophantine>>> dc_t_q;

    private final TRSSubstitution allToX; // see comment to JUST_ONE_VAR

    // For each rule l -> r store a pair of Diophantine formulae:
    // (l >= r, l <= r)
    // Access via method getGeqLeq(Rule).
    private final Map<Rule, Pair<Formula<Diophantine>, Formula<Diophantine>>> ruleGeqLeq;

    private final CondVPCToVPCTransformer deconditionalizer;

    private int nextCoeff; // for creating new coefficients

    private final IndexedNameGenerator hookVarGen; // for creating new hook vars for max(.,.) or min(.,.)

    // which symbols and arg positions get special treatment?
    private final NonMonInterHeuristic interHeuristic;

    // stuff for building Diophantine formulae
    private final FormulaFactory<Diophantine> ffactory;
    private final Formula<Diophantine> ONE;
    private final Formula<Diophantine> ZERO;
    private final SATPatterns<Diophantine> satPatterns;

    private final BigInteger posRange;
    private final BigInteger negRange;
    private final SimplePolynomial negRangePoly;

    private final Map<Rule, String> searchstrictCoeffs;

    private final Map<TRSTerm, OpVarPolynomial> memory; // (unbounded) cache for interpretation
    private final boolean useMemory;

    private final DefaultValueMap<String, BigInteger> ranges;

    /* TODO: settings for the deconditionalizer (CondVP -> VP) */

    /* FIXME: variable names in rules disjoint?! */

    /* Invariant: Always use terms in standard representation! */

    /**
     * for abstract polynomial interpretations
     *
     * @param posRange
     * @param negRange
     */
    private NonMonPoloInterpretation(BigInteger posRange, BigInteger negRange,
            NonMonInterHeuristic interHeuristic) {
        this.interpretation = new LinkedHashMap<FunctionSymbol, OpVarPolynomial>();
        this.fURDirection = new HashMap<FunctionSymbol, Pair<Formula<Diophantine>, Formula<Diophantine>>>();
        this.fIncDec = new HashMap<FunctionSymbol, Pair<Formula<Diophantine>[], Formula<Diophantine>[]>>();
        this.interHeuristic = interHeuristic;
        this.deconditionalizer = new CondVPCToVPCTransformer();
        this.ffactory = new FullSharingFlatteningFactory<Diophantine>();
        this.ruleGeqLeq = new HashMap<Rule, Pair<Formula<Diophantine>, Formula<Diophantine>>>();
        this.ONE  = this.ffactory.buildConstant(true);
        this.ZERO = this.ffactory.buildConstant(false);
        this.ic_t_q = new HashMap<TRSTerm, Map<Position, Formula<Diophantine>>>();
        this.dc_t_q = new HashMap<TRSTerm, Map<Position, Formula<Diophantine>>>();

        // allToX maps all variables to "x" :)
        TRSVariable x = TRSTerm.createVariable(TRSTerm.STANDARD_PREFIX);
        Map<TRSVariable, TRSTerm> protoAllToX = new DefaultValueMap<TRSVariable, TRSTerm>(x);
        this.allToX = TRSSubstitution.create(ImmutableCreator.create(protoAllToX));
        this.satPatterns = new SATPatterns<Diophantine>(this.ffactory);
        this.searchstrictCoeffs = new HashMap<Rule, String>();
        this.nextCoeff = 0;
        this.hookVarGen = new IndexedNameGenerator(NonMonPoloInterpretation.HOOK_PREFIX);
        if (Globals.useAssertions) {
            assert posRange.signum() > 0;
            assert negRange.signum() < 0;
        }
        this.posRange = posRange;
        this.negRange = negRange;
        this.negRangePoly = SimplePolynomial.create(this.negRange);
        this.ranges = new DefaultValueMap<String, BigInteger>(this.posRange.subtract(this.negRange));
        this.memory = new HashMap<TRSTerm, OpVarPolynomial>();
        this.useMemory = true;
    }

    /**
     * for resulting concrete interpretations
     *
     * @param inter
     */
    private NonMonPoloInterpretation(Map<FunctionSymbol, OpVarPolynomial> inter) {
        this.interpretation = inter;
        this.fURDirection = null;
        this.fIncDec = null;
        this.interHeuristic = null;
        this.deconditionalizer = new CondVPCToVPCTransformer();
        this.ffactory = null;
        this.ruleGeqLeq = null;
        this.ONE = null;
        this.ZERO = null;
        this.ic_t_q = null;
        this.dc_t_q = null;
        this.allToX = null;
        this.satPatterns = null;
        this.searchstrictCoeffs = null;
        this.nextCoeff = 0;
        this.hookVarGen = new IndexedNameGenerator(NonMonPoloInterpretation.HOOK_PREFIX);
        this.posRange = BigInteger.ONE; // irrelevant for concrete interpretations
        this.negRange = BigInteger.valueOf(-1l); // irrelevant for concrete interpretations
        this.negRangePoly = null;
        this.ranges = null;
        this.memory = null;
        this.useMemory = false;
    }

    /**
     *
     * @param P
     * @param R
     * @param posRange
     * @param negRange
     * @param allStrict
     * @param interHeuristics
     * @param dioSatConv
     * @param engine
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public static NonMonPOLO solve(QDPProblem qdp,
            BigInteger posRange, BigInteger negRange, boolean allStrict,
            NonMonInterHeuristic interHeuristics,
            DiophantineSATConverter dioSatConv, Engine engine,
            Abortion aborter) throws AbortionException {
        long millisTotal1, millisTotal2;
        millisTotal1 = System.currentTimeMillis();
        NonMonPoloInterpretation inter = new NonMonPoloInterpretation(posRange, negRange,
                interHeuristics);
        NonMonPOLO result = inter.actuallySolve(qdp, allStrict, dioSatConv, engine, aborter);
        millisTotal2 = System.currentTimeMillis();
        if (NonMonPoloInterpretation.log.isLoggable(Level.FINE)) {
            NonMonPoloInterpretation.log.fine("The search for a non-monotonic POLO took " +
                    (millisTotal2 - millisTotal1) + " ms in total.\n");
        }
        return result;
    }


    private NonMonPOLO actuallySolve(QDPProblem qdp,
            boolean allStrict, DiophantineSATConverter dioSatConv, Engine engine,
            Abortion aborter) throws AbortionException {
        Set<Rule> P = qdp.getP();
        Set<Rule> R = qdp.getR();
        long millis1, millis2;

        // 1) Encode to OpVPCs and a SimplePoly (for strictness)
        if (P.size() == 1) {
            allStrict = true;
        }
        millis1 = System.currentTimeMillis();
        Formula<Diophantine> dioFml = this.encodeAllToDioFormula(qdp, allStrict, aborter);

        millis2 = System.currentTimeMillis();

        if (NonMonPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NonMonPoloInterpretation.log.finest("==> In total: Encoding constraints on terms to Diophantine formula took " +
                    (millis2-millis1) + " ms.\n");
        }
        aborter.checkAbortion();

        // solve the diophantineProblem
        DefaultValueMap<String, BigInteger> coeffRanges = this.ranges;

        SearchAlgorithm searchAlg;
        if (engine instanceof SatEngine) {
            SatEngine satEngine = (SatEngine) engine;
            searchAlg = satEngine.getSearchAlgorithm(coeffRanges, dioSatConv);
        }
        else {
            throw new RuntimeException("We currently insist on SAT Engines! Aborting.");
        }

        Map<String, BigInteger> solution = searchAlg.search(dioFml, aborter);

        NonMonPOLO result;
        if (solution == null) {
            result = null;
        }
        else {
            result = this.getSolution(solution, P, R, allStrict, aborter);
        }
        return result;
    }

    /**
     * Encoding Thm. 10 to a Diophantine formula.
     *
     * @param p - p-component of a DP problem
     * @param r - r-component of a DP problem
     * @param allStrict - orient all rules of p strictly?
     * @param aborter
     * @return a formula whose satisfiability means that we can delete some
     *  rules from <code>p</code>.
     */
    private Formula<Diophantine> encodeAllToDioFormula(QDPProblem qdp,
            boolean allStrict, Abortion aborter) throws AbortionException {
        Set<Rule> p = qdp.getP();
        Set<Rule> r = qdp.getR();

        long millis1, millis2;
        /* We are about to build one *huge* Diophantine formula which encodes
         * that the resulting ordering must comply with Thm. 10 and orients
         * at least one/all rules of P (non-capital "p" in Java) strictly.
         * The ingredients are as follows:
         *
         * TODO these docs are outdated, see paper for what is actually
         *      supposed to be done
         *
         * (1) orient P by >_POL (or by >=_POL and >_POL, depending on the
         *     allStrict setting)
         * (2) ensure that (at least) one of (a)-(c) holds:
         *     (a) The main contribution, which consists of all of:
         *         (i) P is POL-non-duplicating (i.e., NDM(P))
         *        (ii) U^{contr}(P) is POL-non-duplicating
         *       (iii) GU(R) is oriented by >=_POL
         *     (b) Consequence of our LPAR'04 paper: Both of
         *         (i) P \cup U(P) is non-duplicating ("classical"
         *             non-duplicatingness regardless of the ordering!)
         *        (ii) U(P) is oriented by =_POL
         *     (c) Hirokawa & Middeldorp, IC'07:
         *         R is oriented by =_POL
         */

        // ad (1):
        millis1 = System.currentTimeMillis();

        // *** "Orient" in the paper (part 1 of 2)
        List<Formula<Diophantine>> resultConjuncts = new ArrayList<Formula<Diophantine>>();
        Formula<Diophantine> f1 = this.encodeOrientP(p, allStrict, aborter);
        resultConjuncts.add(f1);
        millis2 = System.currentTimeMillis();
        if (NonMonPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NonMonPoloInterpretation.log.finest("Encoding Orient for P took " +
                    (millis2-millis1) + " ms.\n");
        }

        // ad (2):
        millis1 = System.currentTimeMillis();

        // *** "Orient" in the paper (part 2 of 2)
        for (Rule rRule : r) {
            //Formula<Diophantine> rRuleIfCondFml = this.encodeRuleForGU(rRule);
            Formula<Diophantine> rRuleIfCondFml = this.encodeOrientedAsGU(rRule);
            resultConjuncts.add(rRuleIfCondFml);
            aborter.checkAbortion();
        }
        millis2 = System.currentTimeMillis();
        if (NonMonPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NonMonPoloInterpretation.log.finest("Encoding Orient for GU(R) took " +
                    (millis2-millis1) + " ms.\n");
        }

        millis1 = System.currentTimeMillis();
        // P and U^{contr}(P) are
        // (1) satisfying
        //     POL-more-monotonicity condition
        // *** "More" in the paper
        // or
        // (2) POL-linear and satisfy
        //     POL-weak-more-monotonicity condition
        // *** "Linear" in the paper
        // *** "Wmore" in the paper

        List<Formula<Diophantine>> moreConjuncts    = new ArrayList<Formula<Diophantine>>(p.size()+r.size());
        List<Formula<Diophantine>> linearAndWmoreConjuncts = new ArrayList<Formula<Diophantine>>(p.size()+r.size());
        for (Rule pRule : p) {
            Formula<Diophantine> linear;
            Pair<Formula<Diophantine>, Formula<Diophantine>> moreWmore;
            linear = this.encodeLinear(pRule, false);
            moreWmore  = this.encodeMoreWmore(pRule, false);

            //duplAndMoreConjuncts.add(duplLinear.x);
            moreConjuncts.add(moreWmore.x);

            linearAndWmoreConjuncts.add(linear);
            linearAndWmoreConjuncts.add(moreWmore.y);

            //Formula<Diophantine> pRuleNonDupMoreMon = this.encodeNonDuplAndMoreMon(pRule, false);
            //resultConjuncts.add(pRuleNonDupMoreMon);
            aborter.checkAbortion();
        }
        for (Rule rRule : r) {
            Formula<Diophantine> linear;
            Pair<Formula<Diophantine>, Formula<Diophantine>> moreWmore;
            linear = this.encodeLinear(rRule, true);
            moreWmore  = this.encodeMoreWmore(rRule, true);

            //duplAndMoreConjuncts.add(duplLinear.x);
            moreConjuncts.add(moreWmore.x);

            linearAndWmoreConjuncts.add(linear);
            linearAndWmoreConjuncts.add(moreWmore.y);

            //Formula<Diophantine> rRuleNonDupMoreMon = this.encodeNonDuplAndMoreMon(rRule, true);
            //resultConjuncts.add(rRuleNonDupMoreMon);
            aborter.checkAbortion();
        }

        Formula<Diophantine> more, linearAndWmore, moreOrLinearWmore;
        more = this.ffactory.buildAnd(moreConjuncts);
        linearAndWmore = this.ffactory.buildAnd(linearAndWmoreConjuncts);
        moreOrLinearWmore = this.ffactory.buildOr(more, NonMonPoloInterpretation.encodeB ? linearAndWmore : this.ZERO);
        // TODO it is not clear whether we want to include part b) of the Thm.
        // in practice. Hence the flag encodeB.

        resultConjuncts.add(moreOrLinearWmore);

        millis2 = System.currentTimeMillis();
        if (NonMonPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NonMonPoloInterpretation.log.finest("Encoding More, Wmore, Dupl, and Linear took " +
                    (millis2-millis1) + " ms.\n");
        }

        millis1 = System.currentTimeMillis();
        // *** "Usable" in the paper
        this.encodeUsable(qdp, resultConjuncts);
        millis2 = System.currentTimeMillis();
        if (NonMonPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NonMonPoloInterpretation.log.finest("Encoding Usable took " +
                    (millis2-millis1) + " ms.\n");
        }

        // derivatives for the sake of connecting ic_f_i and dc_f_i
        // with the polynomial interpretation
        // *** "Compatible" in the paper
        millis1 = System.currentTimeMillis();
        this.encodeCompatible(resultConjuncts);
        millis2 = System.currentTimeMillis();
        if (NonMonPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NonMonPoloInterpretation.log.finest("Encoding Compatible took " +
                    (millis2-millis1) + " ms.\n");
        }

        Formula<Diophantine> result = this.ffactory.buildAnd(resultConjuncts);
        return result;
    }

    /**
     * *** "Orient" (part 1 of 2) in the paper.
     *
     * Requirement (1): P is oriented.
     *
     * @param p
     * @param allStrict
     * @param aborter
     * @return "Orient" for p
     * @throws AbortionException
     */
    private Formula<Diophantine> encodeOrientP(Set<Rule> p,
            boolean allStrict, Abortion aborter) throws AbortionException {
        // conjuncts of the resulting AndFormula
        List<Formula<Diophantine>> cArgs = new ArrayList<Formula<Diophantine>>();

        Set<OpVPC> opVPCs = new LinkedHashSet<OpVPC>(p.size());

        // here we do searchstrict with additional Diophantine variables
        // since using Boolean connectives does not seem beneficial here
        SimplePolynomial sumOfSearchStrictCoeffs = (allStrict) ? null : SimplePolynomial.ZERO;
        for (Rule rule : p) {
            TRSTerm left = rule.getLhsInStandardRepresentation();
            TRSTerm right = rule.getRhsInStandardRepresentation();
            OpVarPolynomial lPol = this.interpretTerm(left);
            OpVarPolynomial rPol = this.interpretTerm(right);
            if (allStrict) {
                rPol = rPol.plus(VarPolynomial.ONE);
            }
            else {
                String searchStrictCoeff = this.getNextSearchStrictCoeff();
                SimplePolynomial searchStrictSP = SimplePolynomial.create(searchStrictCoeff);
                rPol = rPol.plus(VarPolynomial.create(searchStrictSP));
                this.searchstrictCoeffs.put(rule, searchStrictCoeff);
                this.ranges.put(searchStrictCoeff, BigInteger.ONE);
                sumOfSearchStrictCoeffs = sumOfSearchStrictCoeffs.plus(searchStrictSP);
            }
            OpVPC leftGEright = new OpVPC(lPol, rPol, ConstraintType.GE);
            opVPCs.add(leftGEright);
            aborter.checkAbortion();
        }
        Set<VarPolyConstraint> vpcs = this.opVPCsToVPCs(opVPCs);
        for (VarPolyConstraint varPolyConstraint : vpcs) {
            Set<SimplePolyConstraint> absolutelyPositiveConstraints;
            absolutelyPositiveConstraints = varPolyConstraint.createCoefficientConstraints();
            for (SimplePolyConstraint spc : absolutelyPositiveConstraints) {
                if (! spc.isValid()) {
                    Diophantine dio = Diophantine.create(spc);
                    Formula<Diophantine> addMe = this.ffactory.buildTheoryAtom(dio);
                    cArgs.add(addMe);
                }
            }
        }

        if (! allStrict) {
            Diophantine searchStrictDio = Diophantine.create(sumOfSearchStrictCoeffs,
                    SimplePolynomial.ONE, ConstraintType.GE);
            Formula<Diophantine> addMe = this.ffactory.buildTheoryAtom(searchStrictDio);
            cArgs.add(addMe);
        }
        Formula<Diophantine> result = this.ffactory.buildAnd(cArgs);
        return result;
    }

    /**
     * *** "Linear" in the paper
     * (on a per-rule-basis)
     * -> was added in a later version of the paper, corresponding code is marked
     *
     * @param rule
     * @param requireLRootUsable - do we encode for a rule from R?
     * @return "Dupl" and "Linear" for rule
     */
    private Formula<Diophantine> encodeLinear(Rule rule, boolean requireLRootUsable) {
        TRSFunctionApplication left  = rule.getLhsInStandardRepresentation();
        TRSTerm right = rule.getRhsInStandardRepresentation();
        Map<TRSVariable, List<Position>> rVarToPositions = right.getVariablePositions();
        Map<TRSVariable, List<Position>> lVarToPositions =  left.getVariablePositions();

        // in case we have a (possibly) usable rule and not a dependency pair,
        // we must require that the rule is in fact usable, otherwise we need
        // not fulfill the non-duplicatingness and more-monotonicity requirements
        Formula<Diophantine> lRootUsable;
        if (requireLRootUsable) {
            FunctionSymbol lRoot = left.getRootSymbol();
            Pair<Formula<Diophantine>, Formula<Diophantine>> urDirection = this.getURDirection(lRoot);
            lRootUsable = this.ffactory.buildOr(urDirection.x, urDirection.y);
        }
        else {
            lRootUsable = null;
        }

        /*
        // stage 1: encode that for each var x of r, there are not more
        // dependent occurrences of x on the rhs than on the lhs
        List<Formula<Diophantine>> duplResArgs   = new ArrayList<Formula<Diophantine>>(rVarToPositions.size());

        for (Entry<Variable, List<Position>> xToPsRHS : rVarToPositions.entrySet()) {
            List<Position> rhsPs = xToPsRHS.getValue();
            List<Formula<Diophantine>> rhsDeps = new ArrayList<Formula<Diophantine>>(rhsPs.size());
            for (Position p : rhsPs) {
                Formula<Diophantine> dep = this.dep(right, p);
                rhsDeps.add(dep);
            }
            List<Position> lhsPs = lVarToPositions.get(xToPsRHS.getKey());
            List<Formula<Diophantine>> lhsDeps = new ArrayList<Formula<Diophantine>>(lhsPs.size());
            for (Position p : lhsPs) {
                Formula<Diophantine> dep = this.dep(left, p);
                lhsDeps.add(dep);
            }
            Formula<Diophantine> duplDepCountOkForX = this.satPatterns.encodeXsAtLeastAsManyTrueAsYs(lhsDeps, rhsDeps);

            if (requireLRootUsable) {
                duplDepCountOkForX = this.ffactory.buildImplication(lRootUsable, duplDepCountOkForX);
            }
            duplResArgs.add(duplDepCountOkForX);
        }*/

        // special code inserted for "Linear"
        List<Formula<Diophantine>> linearResArgs = new ArrayList<Formula<Diophantine>>(lVarToPositions.size());
        for (Entry<TRSVariable, List<Position>> xToPsLHS : lVarToPositions.entrySet()) {
            List<Position> lhsPs = xToPsLHS.getValue();
            List<Formula<Diophantine>> lhsDeps = new ArrayList<Formula<Diophantine>>(lhsPs.size());
            if (! NonMonPoloInterpretation.RIGHT_LINEAR_SUFFICES) {
                for (Position p : lhsPs) {
                    Formula<Diophantine> dep = this.dep(left, p);
                    lhsDeps.add(dep);
                }
            }
            List<Position> rhsPs = rVarToPositions.get(xToPsLHS.getKey());
            List<Formula<Diophantine>> rhsDeps;
            if (rhsPs == null) { // not every var of left also occurs in right
                rhsDeps = Collections.<Formula<Diophantine>>emptyList();
            }
            else {
                rhsDeps = new ArrayList<Formula<Diophantine>>(rhsPs.size());
                for (Position p : rhsPs) {
                    Formula<Diophantine> dep = this.dep(right, p);
                    rhsDeps.add(dep);
                }
            }

            Formula<Diophantine> lhsLinearDepCountOkForX,
                    rhsLinearDepCountOkForX, linearDepCountOkForX;
            if (! NonMonPoloInterpretation.RIGHT_LINEAR_SUFFICES) {
                lhsLinearDepCountOkForX = this.satPatterns.encodeAtMostOne(lhsDeps);
                rhsLinearDepCountOkForX = this.satPatterns.encodeAtMostOne(rhsDeps);
                linearDepCountOkForX = this.ffactory.buildAnd(lhsLinearDepCountOkForX, rhsLinearDepCountOkForX);
            }
            else {
                linearDepCountOkForX = this.satPatterns.encodeAtMostOne(rhsDeps);
            }

            if (requireLRootUsable) {
                linearDepCountOkForX = this.ffactory.buildImplication(lRootUsable, linearDepCountOkForX);
            }
            linearResArgs.add(linearDepCountOkForX);
        }
        // end special code

        //Formula<Diophantine> duplRes   = this.ffactory.buildAnd(duplResArgs);
        Formula<Diophantine> linearRes = this.ffactory.buildAnd(linearResArgs);
        return linearRes;
    }


    /**
     * x:
     * *** "More" in the paper
     * (on a per-rule-basis)
     *
     * y:
     * *** "Wmore" in the paper
     * (on a per-rule-basis)
     *
     * @param rule
     * @param requireLRootUsable - do we encode for a rule from R?
     * @return "More" and "Wmore" for rule
     */
    private Pair<Formula<Diophantine>, Formula<Diophantine>> encodeMoreWmore(Rule rule,
                boolean requireLRootUsable) {
        TRSFunctionApplication left = rule.getLhsInStandardRepresentation();
        TRSTerm right = rule.getRhsInStandardRepresentation();
        Map<TRSVariable, List<Position>> rVarToPositions = right.getVariablePositions();
        Map<TRSVariable, List<Position>> lVarToPositions =  left.getVariablePositions();
        Formula<Diophantine> lRootUsable;
        if (requireLRootUsable) {
            FunctionSymbol lRoot = left.getRootSymbol();
            Pair<Formula<Diophantine>, Formula<Diophantine>> urDirection = this.getURDirection(lRoot);
            lRootUsable = this.ffactory.buildOr(urDirection.x, urDirection.y);
        }
        else {
            lRootUsable = null;
        }

        List<Formula<Diophantine>> resArgs     = new ArrayList<Formula<Diophantine>>();
        List<Formula<Diophantine>> weakResArgs = new ArrayList<Formula<Diophantine>>();
        for (Entry<TRSVariable, List<Position>> xToPs : rVarToPositions.entrySet()) {
            List<Position> rhsPs = xToPs.getValue();
            List<Position> lhsPs = lVarToPositions.get(xToPs.getKey());

            Formula<Diophantine> mm = this.encodeMM(left, right, lhsPs, rhsPs);

            // first treat "normal" more
            if (requireLRootUsable) {
                resArgs.add(this.ffactory.buildImplication(lRootUsable, mm));
            }
            else {
                resArgs.add(mm);
            }

            // now build special stuff for /weak/ more
            List<Formula<Diophantine>> lhsDeps = new ArrayList<Formula<Diophantine>>(lhsPs.size());
            for (Position p : lhsPs) {
                Formula<Diophantine> dep = this.dep(left, p);
                lhsDeps.add(dep);
            }
            Formula<Diophantine> oneDepXOnLhs, premise;
            oneDepXOnLhs = this.satPatterns.encodeExactlyOne(lhsDeps);
            if (requireLRootUsable) {
                premise = this.ffactory.buildAnd(lRootUsable, oneDepXOnLhs);
            }
            else {
                premise = oneDepXOnLhs;
            }
            weakResArgs.add(this.ffactory.buildImplication(premise, mm));
        }
        Formula<Diophantine> res     = this.ffactory.buildAnd(resArgs);
        Formula<Diophantine> weakRes = this.ffactory.buildAnd(weakResArgs);

        Pair<Formula<Diophantine>, Formula<Diophantine>> result;
        result = new Pair<Formula<Diophantine>, Formula<Diophantine>>(res, weakRes);
        return result;
    }

    /**
     * Corresponds to mm(l -> r, x) in the paper. Here, varPositions
     * are the positions of x in l.
     *
     * @param l
     * @param r
     * @param lPos - positions of the variable in question in l
     * @param rPos - positions of the variable in question in r
     * @return
     */
    private Formula<Diophantine> encodeMM(TRSFunctionApplication l, TRSTerm r,
            List<Position> lPos, List<Position> rPos) {
        // We are going to need ic(l, p), dc(l, p), ic(r, p) and dc(l, p)
        // for all p in varPositions. Compute and store them.
        int lSize = lPos.size();
        int rSize = rPos.size();

        List<Formula<Diophantine>> lWildMon, lIncMon, lDecMon,
                                   rWildMon, rIncMon, rDecMon;
        lWildMon = new ArrayList<Formula<Diophantine>>(lSize);
        lIncMon = new ArrayList<Formula<Diophantine>>(lSize);
        lDecMon = new ArrayList<Formula<Diophantine>>(lSize);
        rWildMon = new ArrayList<Formula<Diophantine>>(rSize);
        rIncMon = new ArrayList<Formula<Diophantine>>(rSize);
        rDecMon = new ArrayList<Formula<Diophantine>>(rSize);

        for (Position p : lPos) {
            Formula<Diophantine> ilp, dlp, notIlp, notDlp;
            ilp = this.ic(l, p);
            dlp = this.dc(l, p);
            notIlp = this.ffactory.buildNot(ilp);
            notDlp = this.ffactory.buildNot(dlp);
            lWildMon.add(this.ffactory.buildAnd(notIlp, notDlp));
            lIncMon.add(this.ffactory.buildAnd(ilp, notDlp));
            lDecMon.add(this.ffactory.buildAnd(notIlp, dlp));
        }
        for (Position p : rPos) {
            Formula<Diophantine> irp, drp, notIrp, notDrp;
            irp = this.ic(r, p);
            drp = this.dc(r, p);
            notIrp = this.ffactory.buildNot(irp);
            notDrp = this.ffactory.buildNot(drp);
            rWildMon.add(this.ffactory.buildAnd(notIrp, notDrp));
            rIncMon.add(this.ffactory.buildAnd(irp, notDrp));
            rDecMon.add(this.ffactory.buildAnd(notIrp, drp));
        }

        List<Formula<Diophantine>> lWildMonCount, lIncMonCount, lDecMonCount,
                                   rWildMonCount, rIncMonCount, rDecMonCount;

        lWildMonCount = this.satPatterns.sumUp(lWildMon);
        lIncMonCount  = this.satPatterns.sumUp(lIncMon);
        lDecMonCount  = this.satPatterns.sumUp(lDecMon);
        rWildMonCount = this.satPatterns.sumUp(rWildMon);
        rIncMonCount  = this.satPatterns.sumUp(rIncMon);
        rDecMonCount  = this.satPatterns.sumUp(rDecMon);

        // We will have several conjuncts:
        // (1) for monotonicity specification \emptyset (i.e., wild)
        // (2) for monotonicity specification {ic} (i.e., ic)
        // (3) for monotonicity specification {dc} (i.e., dc)
        // (4) all the side conjuncts due to the introduction of
        //     "encoded Diophantine variables", i.e., formula tuples,
        //     if the range is not 2^k - 1 for some k
        List<Formula<Diophantine>> conjuncts = new ArrayList<Formula<Diophantine>>();
        Pair<List<Formula<Diophantine>>, List<Formula<Diophantine>>> pIncWithSideConjuncts, pDecWithSideConjuncts;
        pIncWithSideConjuncts = this.encodeDioVar(lSize);
        pDecWithSideConjuncts = this.encodeDioVar(lSize);
        List<Formula<Diophantine>> pInc, pDec;
        pInc = pIncWithSideConjuncts.x;
        pDec = pDecWithSideConjuncts.x;

        // ad (1):
        {
            // "smaller side" of wild ineq:
            List<Formula<Diophantine>> wildRhs = this.satPatterns.buildPlus(pInc, pDec);
            wildRhs = this.satPatterns.buildPlus(wildRhs, rWildMonCount);
            // "bigger side" of wild ineq is just lWildMonCount
            conjuncts.add(this.satPatterns.buildGECircuit(lWildMonCount, wildRhs));
        }

        // ad (2):
        {
            // "bigger side" of inc ineq:
            List<Formula<Diophantine>> incLhs = this.satPatterns.buildPlus(lIncMonCount, pInc);
            conjuncts.add(this.satPatterns.buildGECircuit(incLhs, rIncMonCount));
        }

        // ad (3):
        {
            // "bigger side" of dec ineq:
            List<Formula<Diophantine>> decLhs = this.satPatterns.buildPlus(lDecMonCount, pDec);
            conjuncts.add(this.satPatterns.buildGECircuit(decLhs, rDecMonCount));
        }

        // ad(4):
        conjuncts.addAll(pIncWithSideConjuncts.y);
        conjuncts.addAll(pDecWithSideConjuncts.y);
        Formula<Diophantine> result = this.ffactory.buildAnd(conjuncts);
        return result;
    }

    /**
     *
     * @param r - the range, must be >= 1
     * @return x: the encoding of the variable
     *         y: side conjuncts to make sure that r is not exceeded
     */
    private Pair<List<Formula<Diophantine>>, List<Formula<Diophantine>>> encodeDioVar(int r) {
        if (Globals.useAssertions) {
            assert r >= 1;
        }
        int bitLength = AProVEMath.binaryLength(r);
        List<Formula<Diophantine>> propVars = new ArrayList<Formula<Diophantine>>(bitLength);
        for (int i = 0; i < bitLength; ++i) {
            Formula<Diophantine> var = this.ffactory.buildVariable();
            propVars.add(var);
        }
        List<Formula<Diophantine>> sideConjuncts = this.excludeUpperBits(r, propVars);
        return new Pair<List<Formula<Diophantine>>, List<Formula<Diophantine>>>(propVars,
                sideConjuncts);
    }

    /**
     * Helper method for allowing arbitrary natural ranges for
     * Diophantine variables, not only 2^k - 1. Generates clauses
     * that prohibit values greater than range.
     *
     * @param range - maximum range allowed for vars;
     *  may be at most 2^vars.size() - 1
     * @param variables - tuple of variables (formulae) that is supposed
     *  to represent some Diophantine variable
     * @return conjuncts for enforcing that I(vars) <= range for
     *  any model I of the circuit in construction
     */
    private List<Formula<Diophantine>> excludeUpperBits(int range, List<Formula<Diophantine>> vars) {
        int bits = vars.size();
        if (Globals.useAssertions) {
            assert bits >= AProVEMath.binaryLength(range);
        }

        if (Integer.bitCount(range) == bits) {
            return Collections.<Formula<Diophantine>>emptyList();
        }

        int max = AProVEMath.power(2, bits) - 1;

        List<Formula<Diophantine>> notVars = new ArrayList<Formula<Diophantine>>(bits);
        for (int i = 0; i < vars.size(); ++i) {
            notVars.add(this.ffactory.buildNot(vars.get(i)));
        }

        List<Formula<Diophantine>> result = new ArrayList<Formula<Diophantine>>(max - range);
        for (int i = range + 1; i <= max; ++i) {
            List<Formula<Diophantine>> disjuncts = new ArrayList<Formula<Diophantine>>(bits);
            for (int j = 0; j < bits; ++j) {
                if ((i & (1 << j)) != 0) {
                    disjuncts.add(notVars.get(j));
                }
                else {
                    disjuncts.add(vars.get(j));
                }
            }
            result.add(this.ffactory.buildOr(disjuncts));
        }
        return result;
    }


    /**
     * *** "Orient" (part 2 of 2) in the paper
     *
     * Computes "Orient" for a rule of R.
     *
     * @param rule
     * @return
     */
    private Formula<Diophantine> encodeOrientedAsGU(Rule rule) {
        // First get the interpretations of rule in both directions.
        // Interpret the terms in rule only once, OpVarPolynomial handling is
        // expensive.
        Pair<Formula<Diophantine>, Formula<Diophantine>> geqLeq = this.getGeqLeq(rule);
        FunctionSymbol lRoot = rule.getRootSymbol();

        // (us_f -> f(...) >= r) and (\overline{us_f} -> r >= f(...))
        Pair<Formula<Diophantine>, Formula<Diophantine>> urDirection = this.getURDirection(lRoot);
        Formula<Diophantine> normalUsable   = this.ffactory.buildImplication(urDirection.x, geqLeq.x);
        Formula<Diophantine> reversedUsable = this.ffactory.buildImplication(urDirection.y, geqLeq.y);
        Formula<Diophantine> result = this.ffactory.buildAnd(normalUsable, reversedUsable);
        return result;
    }

    /**
     * *** "Usable" in the paper
     *
     * @param p - pairs
     * @param r - (possibly usable) rules
     * @param resConjucts - the constraints are added here
     */
    private void encodeUsable(QDPProblem qdp, List<Formula<Diophantine>> resConjuncts) {
        Set<FunctionSymbol> defSyms = qdp.getRwithQ().getDefinedSymbolsOfR();
        Set<Rule> p = qdp.getP();

        // pairs: defined syms in rhs make the corresponding rules usable
        for (Rule pRule : p) {
            TRSTerm rhs = pRule.getRight();
            Collection<Pair<Position, TRSTerm>> posAndSubs = rhs.getPositionsWithSubTerms();
            for (Pair<Position, TRSTerm> posSub : posAndSubs) {
                TRSTerm sub = posSub.y;
                if (! sub.isVariable()) {
                    FunctionSymbol f = ((TRSFunctionApplication) sub).getRootSymbol();
                    if (defSyms.contains(f)) {
                        // so sub is a defined subterm of the rhs :)
                        Pair<Formula<Diophantine>, Formula<Diophantine>> usPs;
                        usPs = this.encodeUsableBasedOnMon(rhs, posSub.x, f, false);

                        // we need that functions that are called in the rhs
                        // of P in any case, so no need for additional
                        // requirements here.
                        resConjuncts.add(usPs.x);
                        resConjuncts.add(usPs.y);
                    }
                }
            }
        }

        // similar for the rules, but here we need to know which symbol
        // roots the corresponding lhs
        Map<FunctionSymbol, ImmutableSet<Rule>> fsToRules = qdp.getRwithQ().getRuleMap();
        for (Entry<FunctionSymbol, ImmutableSet<Rule>> fToRules : fsToRules.entrySet()) {
            FunctionSymbol f = fToRules.getKey();
            Pair<Formula<Diophantine>, Formula<Diophantine>> usDirF = this.getURDirection(f);
            for (Rule fRule : fToRules.getValue()) {
                TRSTerm rhs = fRule.getRight();
                Collection<Pair<Position, TRSTerm>> posAndSubs = rhs.getPositionsWithSubTerms();
                for (Pair<Position, TRSTerm> posSub : posAndSubs) {
                    TRSTerm sub = posSub.y;
                    if (! sub.isVariable()) {
                        FunctionSymbol g = ((TRSFunctionApplication) sub).getRootSymbol();
                        if (defSyms.contains(g)) {
                            // so sub is a defined subterm of the rhs :)

                            // for R, we must think of both directions and also of
                            // conditions: only if f is usable, a rule
                            // f(...) -> ...g(...)... actually matters.

                            Pair<Formula<Diophantine>, Formula<Diophantine>> usRs1, usRs2;
                            usRs1 = this.encodeUsableBasedOnMon(rhs, posSub.x, g, false);
                            usRs2 = this.encodeUsableBasedOnMon(rhs, posSub.x, g, true);
                            Formula<Diophantine> conclusionUs1, conclusionUs2, implicationUs1, implicationUs2;
                            conclusionUs1  = this.ffactory.buildAnd(usRs1.x, usRs1.y);
                            conclusionUs2  = this.ffactory.buildAnd(usRs2.x, usRs2.y);
                            implicationUs1 = this.ffactory.buildImplication(usDirF.x, conclusionUs1);
                            implicationUs2 = this.ffactory.buildImplication(usDirF.y, conclusionUs2);
                            resConjuncts.add(implicationUs1);
                            resConjuncts.add(implicationUs2);
                        }
                    }
                }
            }
        }
    }


    /**
     * Auxiliary method for inner implications in encodeUsable.
     *
     * @param t
     * @param p
     * @param f
     * @param inverse - set to true if you are in a
     *  "monotonically decreasing context"
     * @param resConjuncts - the constraints are added here
     */
    private Pair<Formula<Diophantine>, Formula<Diophantine>> encodeUsableBasedOnMon(TRSTerm t,
            Position p, FunctionSymbol f, boolean inverse) {
        Formula<Diophantine> dc_t_p = this.dc(t, p);
        Formula<Diophantine> ic_t_p = this.ic(t, p);
        Pair<Formula<Diophantine>, Formula<Diophantine>> usableDir = this.getURDirection(f);

        Formula<Diophantine> dcRhs = inverse ? usableDir.y : usableDir.x;
        Formula<Diophantine> icRhs = inverse ? usableDir.x : usableDir.y;

        // "not x => y" is equivalent to "x or y", so just use the latter
        Formula<Diophantine> res1 = this.ffactory.buildOr(dc_t_p, dcRhs);
        Formula<Diophantine> res2 = this.ffactory.buildOr(ic_t_p, icRhs);
        return new Pair<Formula<Diophantine>, Formula<Diophantine>>(res1, res2);
    }

    /*
    private Formula<Diophantine> encodeRuleForGU(Rule rule) {
        // First get the interpretations of rule in both directions.
        // Interpret the terms in rule only once, OpVarPolynomial handling is
        // expensive.
        Pair<Formula<Diophantine>, Formula<Diophantine>> geqLeq = this.getGeqLeq(rule);

        // POL-non-duplicatingness
        Formula<Diophantine> ndm = this.encodeNonDuplAndMoreMon(rule);

        // 1) Wild monotonicity behavior. Just orient the rules in both directions.
        Formula<Diophantine> wild = this.ffactory.buildAnd(geqLeq.x, geqLeq.y, ndm);

        // 2) For each of the disjuncts of qac:
        //      We have a filtering (mon inc. and dec. at some position)
        //      or we have a clear monotonicity tendency (the two cases overlap,
        //      but that is okay).
        List<Formula<Diophantine>> cArgs = new ArrayList<Formula<Diophantine>>();
        Set<? extends Set<Pair<FunctionSymbol, Integer>>> qacDNF = qac.getSetRepresentation();
        for (Set<Pair<FunctionSymbol, Integer>> qacDisjunct : qacDNF) {
            // (a) filtered
            List<Formula<Diophantine>> monIncAndDecCArgs = new ArrayList<Formula<Diophantine>>();
            List<Formula<Diophantine>> dcs = new ArrayList<Formula<Diophantine>>();
            for (Pair<FunctionSymbol, Integer> fAndI : qacDisjunct) {
                Pair<Formula<Diophantine>[], Formula<Diophantine>[]> fIncDec = this.getIncDec(fAndI.x);
                int i = fAndI.y;
                Formula<Diophantine> fMonIncAndDecAtI = this.ffactory.buildOr(fIncDec.x[i], fIncDec.y[i]);
                monIncAndDecCArgs.add(fMonIncAndDecAtI);

                // for later
                dcs.add(fIncDec.y[i]);
            }
            Formula<Diophantine> monIncAndDec = this.ffactory.buildAnd(monIncAndDecCArgs);

            // (b) clear monotonicity behavior
            Formula<Diophantine> oddDCs = this.satPatterns.encodeOdd(dcs);
            // if odd number of dc's set  then r >= l else  l >= r
            Formula<Diophantine> orientInWhichDirection = this.ffactory.buildIte(oddDCs,
                    geqLeq.y, geqLeq.x);
            Formula<Diophantine> orientAndNDM = this.ffactory.buildAnd(orientInWhichDirection, ndm);

            Formula<Diophantine> currentQacDisjunctFormula = this.ffactory.buildOr(monIncAndDec, orientAndNDM);
            cArgs.add(currentQacDisjunctFormula);
        }

        Formula<Diophantine> ruleOccursMonotonically = this.ffactory.buildAnd(cArgs);

        Formula<Diophantine> result = this.ffactory.buildOr(wild,
                ruleOccursMonotonically);
        return result;
    }
    */

    /**
     * *** "Compat" in the paper
     *
     * @param resultConjuncts - the conjuncts that assert compatibility
     *  will be added here
     */
    private void encodeCompatible(List<Formula<Diophantine>> resultConjuncts) {
        // gotta make sure that all the ic's and the dc's take sensible values
        // => fun with derivatives!
        for (Entry<FunctionSymbol, OpVarPolynomial> fInter : this.interpretation.entrySet()) {
            FunctionSymbol f = fInter.getKey();
            OpVarPolynomial fPol = fInter.getValue();

            OpVPC leftEQright = new OpVPC(fPol, OpVarPolynomial.ZERO, ConstraintType.EQ);
            VPSubstitutor substitutor = new VPSubstitutor();

            // fPol >= 0, fPol <= 0 as CondVPCs
            // note: must not drop constraints with valid conclusions
            // before deriving! deriving may render them invalid.
            Pair<Set<CondVPC>, Set<CondVPC>> condVPCsPair = leftEQright.toCondVPCsPair(substitutor, false);

            Pair<Formula<Diophantine>[], Formula<Diophantine>[]> fIcDc = this.getIncDec(f);
            Formula<Diophantine>[] ic = fIcDc.x;
            Formula<Diophantine>[] dc = fIcDc.y;

            // now derive them wrt to all vars x_1, ..., x_n, respectively.
            int arity = f.getArity();
            for (int i = 0; i < arity; ++i) {
                String xi = NonMonPoloInterpretation.VAR_PREFIX + (i+1);
                Set<CondVPC> derivativeGEzero = CondVPC.deriveAllWRT(condVPCsPair.x, xi, false);
                Set<CondVPC> derivativeLEzero = CondVPC.deriveAllWRT(condVPCsPair.y, xi, false);

                Set<VarPolyConstraint> vpcsGE, vpcsLE;
                vpcsGE = this.deconditionalizer.transform(derivativeGEzero, this.ranges);
                vpcsLE = this.deconditionalizer.transform(derivativeLEzero, this.ranges);

                // expresses d f_Pol / d xi >= 0
                Formula<Diophantine> geFml = this.encodeVpcs(vpcsGE);

                // expresses d f_Pol / d xi <= 0
                Formula<Diophantine> leFml = this.encodeVpcs(vpcsLE);

                Formula<Diophantine> icImpliesDerGE0 = this.ffactory.buildImplication(ic[i], geFml);
                Formula<Diophantine> dcImpliesDerLE0 = this.ffactory.buildImplication(dc[i], leFml);

                resultConjuncts.add(icImpliesDerGE0);
                resultConjuncts.add(dcImpliesDerLE0);
            }
        }
    }



    private Formula<Diophantine> encodeVpcs(Set<VarPolyConstraint> vpcs) {
        Formula<Diophantine> result;
        List<Formula<Diophantine>> fmlae = new ArrayList<Formula<Diophantine>>();
        for (VarPolyConstraint varPolyConstraint : vpcs) {
            Set<SimplePolyConstraint> absolutelyPositiveConstraints;
            absolutelyPositiveConstraints = varPolyConstraint.createCoefficientConstraints();
            for (SimplePolyConstraint spc : absolutelyPositiveConstraints) {
                if (! spc.isValid()) {
                    Diophantine dio = Diophantine.create(spc);
                    Formula<Diophantine> addMe = this.ffactory.buildTheoryAtom(dio);
                    fmlae.add(addMe);
                }
            }
        }
        result = this.ffactory.buildAnd(fmlae);
        return result;
    }

    // The names of the following three methods are taken from
    // the corresponding formulae in the paper.

    /**
     * Call with sane values only.
     *
     * @param t
     * @param q
     * @return a formula ic(t, q) such that if ic(t, q) holds, then
     *  t is monotonically increasing in position q.
     */
    private Formula<Diophantine> ic(TRSTerm t, Position q) {
        // TODO caching okay?!
        Formula<Diophantine> res = null;
        if (NonMonPoloInterpretation.JUST_ONE_VAR) {
            t = t.applySubstitution(this.allToX);
        }
        Map<Position, Formula<Diophantine>> posToFml = this.ic_t_q.get(t);
        boolean termHasNoMapYet = false;
        if (posToFml == null) {
            termHasNoMapYet = true;
            posToFml = new HashMap<Position, Formula<Diophantine>>();
        }
        else {
            res = posToFml.get(q);
        }
        if (res == null) {
            if (q.isEmptyPosition()) {
                res = this.ONE;
            }
            else {
                // q has the form i.p
                Position p = q.tail(1);
                if (Globals.useAssertions) {
                    assert ! t.isVariable();
                }
                TRSFunctionApplication fApp = (TRSFunctionApplication) t;
                int i = q.firstIndex();
                TRSTerm ti = fApp.getArgument(i);
                FunctionSymbol f = fApp.getRootSymbol();

                Pair<Formula<Diophantine>[], Formula<Diophantine>[]> incDec = this.getIncDec(f);
                List<Formula<Diophantine>> resDisjuncts = new ArrayList<Formula<Diophantine>>(4);
                Formula<Diophantine> ic_f_i  = incDec.x[i];
                Formula<Diophantine> ic_ti_p = this.ic(ti, p);
                Formula<Diophantine> dc_f_i  = incDec.y[i];
                Formula<Diophantine> dc_ti_p = this.dc(ti, p);
                resDisjuncts.add(this.ffactory.buildAnd(ic_f_i,  ic_ti_p));
                resDisjuncts.add(this.ffactory.buildAnd(dc_f_i,  dc_ti_p));
                resDisjuncts.add(this.ffactory.buildAnd(ic_f_i,  dc_f_i));
                resDisjuncts.add(this.ffactory.buildAnd(ic_ti_p, dc_ti_p));
                res = this.ffactory.buildOr(resDisjuncts);
            }
            posToFml.put(q, res);
            if (termHasNoMapYet) {
                this.ic_t_q.put(t, posToFml);
            }
        }
        return res;
    }

    /**
     * Call with sane values only.
     *
     * @param t
     * @param q
     * @return a formula dc(t, q) such that if dc(t, q) holds, then
     *  t is monotonically decreasing in position q.
     */
    private Formula<Diophantine> dc(TRSTerm t, Position q) {
        Formula<Diophantine> res = null;
        if (NonMonPoloInterpretation.JUST_ONE_VAR) {
            t = t.applySubstitution(this.allToX);
        }
        Map<Position, Formula<Diophantine>> posToFml = this.dc_t_q.get(t);
        boolean termHasNoMapYet = false;
        if (posToFml == null) {
            termHasNoMapYet = true;
            posToFml = new HashMap<Position, Formula<Diophantine>>();
        }
        else {
            res = posToFml.get(q);
        }
        if (res == null) {
            if (q.isEmptyPosition()) {
                return this.ZERO;
            }
            else {
                // q has the form i.p
                Position p = q.tail(1);
                if (Globals.useAssertions) {
                    assert ! t.isVariable();
                }
                TRSFunctionApplication fApp = (TRSFunctionApplication) t;
                int i = q.firstIndex();
                TRSTerm ti = fApp.getArgument(i);
                FunctionSymbol f = fApp.getRootSymbol();

                Pair<Formula<Diophantine>[], Formula<Diophantine>[]> incDec = this.getIncDec(f);
                List<Formula<Diophantine>> resDisjuncts = new ArrayList<Formula<Diophantine>>(4);
                Formula<Diophantine> ic_f_i  = incDec.x[i];
                Formula<Diophantine> ic_ti_p = this.ic(ti, p);
                Formula<Diophantine> dc_f_i  = incDec.y[i];
                Formula<Diophantine> dc_ti_p = this.dc(ti, p);
                resDisjuncts.add(this.ffactory.buildAnd(ic_f_i,  dc_ti_p));
                resDisjuncts.add(this.ffactory.buildAnd(dc_f_i,  ic_ti_p));
                resDisjuncts.add(this.ffactory.buildAnd(ic_f_i,  dc_f_i));
                resDisjuncts.add(this.ffactory.buildAnd(ic_ti_p, dc_ti_p));
                res = this.ffactory.buildOr(resDisjuncts);
            }
            posToFml.put(q, res);
            if (termHasNoMapYet) {
                this.dc_t_q.put(t, posToFml);
            }
        }
        return res;
    }

    /**
     * Call with sane values only.
     *
     * @param t
     * @param q
     * @return a formula that encodes that t may be dependent on q, i.e.,
     *  (! ic(t,q) || ! dc(t,q))
     */
    private Formula<Diophantine> dep(TRSTerm t, Position q) {
        Formula<Diophantine> ic = this.ic(t, q);
        Formula<Diophantine> dc = this.dc(t, q);
        Formula<Diophantine> result = this.notBoth(ic, dc);
        return result;
    }

    private Formula<Diophantine> notBoth(Formula<Diophantine> f1,
                Formula<Diophantine> f2) {
        // TODO try  "not (ic and dc)"  instead
        return this.ffactory.buildOr(this.ffactory.buildNot(f1),
                this.ffactory.buildNot(f2));
    }

    /**
     * Uses this.ruleGeqLeq as (unbounded) cache.
     *
     * @param rule
     * @return pair of Diophantine formulae:<br>
     *  1st component encodes l >= r, 2nd component encodes l <= r
     */
    private Pair<Formula<Diophantine>, Formula<Diophantine>> getGeqLeq(Rule rule) {
        Pair<Formula<Diophantine>, Formula<Diophantine>> result;
        result = this.ruleGeqLeq.get(rule);
        if (result == null) {
            TRSTerm left = rule.getLhsInStandardRepresentation();
            TRSTerm right = rule.getRhsInStandardRepresentation();
            OpVarPolynomial lPol = this.interpretTerm(left);
            OpVarPolynomial rPol = this.interpretTerm(right);
            OpVPC leftEQright = new OpVPC(lPol, rPol, ConstraintType.EQ);

            VPSubstitutor substitutor = new VPSubstitutor();
            Pair<Set<CondVPC>, Set<CondVPC>> condVPCsPair = leftEQright.toCondVPCsPair(substitutor);

            Set<VarPolyConstraint> vpcsGE, vpcsLE;
            vpcsGE = this.deconditionalizer.transform(condVPCsPair.x, this.ranges);
            vpcsLE = this.deconditionalizer.transform(condVPCsPair.y, this.ranges);

            Formula<Diophantine> geFml = this.encodeVpcs(vpcsGE);
            Formula<Diophantine> leFml = this.encodeVpcs(vpcsLE);
            result = new Pair<Formula<Diophantine>, Formula<Diophantine>>(geFml, leFml);
        }
        return result;
    }

    /**
     * Uses this.fURDirection as (unbounded) cache.
     *
     * @param rule
     * @return pair of Diophantine formulae:<br>
     *  1st component encodes "us_f", 2nd component encodes "\overline{us}_f", i.e.,
     *  - 1st component true means that the f-rules must be oriented in normal direction and
     *  - 2nd component true means that the f-rules must be oriented in reversed direction
     */
    private Pair<Formula<Diophantine>, Formula<Diophantine>> getURDirection(FunctionSymbol f) {
        Pair<Formula<Diophantine>, Formula<Diophantine>> res = this.fURDirection.get(f);
        if (res == null) {
            Formula<Diophantine> normal  = this.ffactory.buildVariable();
            Formula<Diophantine> reverse = this.ffactory.buildVariable();
            res = new Pair<Formula<Diophantine>, Formula<Diophantine>>(normal, reverse);
            this.fURDirection.put(f, res);
        }
        return res;
    }

    /**
     * Uses this.fIncDec as (unbounded) cache.
     *
     * @param f - function symbol of arity n
     * @return pair of arrays of length n of Diophantine formulae:<br>
     *  i-th entry in 1st component encodes "ic(f,i)" (f mon. inc. in i-th arg),
     *  i-th entry in 2nd component encodes "dc(f,i)" (f mon. dec. in i-th arg)
     *  (in later versions of the paper, arrows pointing up/down were used
     *   instead of "ic"/"dc")
     */
    private Pair<Formula<Diophantine>[], Formula<Diophantine>[]> getIncDec(FunctionSymbol f) {
        Pair<Formula<Diophantine>[], Formula<Diophantine>[]> res = this.fIncDec.get(f);
        if (res == null) {
            int n = f.getArity();
            Formula<Diophantine>[] ic = new Formula[n];
            Formula<Diophantine>[] dc = new Formula[n];
            for (int i = 0; i < n; ++i) {
                ic[i] = this.ffactory.buildVariable();
                dc[i] = this.ffactory.buildVariable();
            }
            res = new Pair<Formula<Diophantine>[], Formula<Diophantine>[]>(ic, dc);
            this.fIncDec.put(f, res);
        }
        return res;
    }


    /**
     * Converts a Diophantine model to the NegPolo ordering, i.e.,
     * specializes this based on the model.
     *
     * @param assignment
     * @return
     */
    private NonMonPOLO getSolution(Map<String, BigInteger> assignment,
            Set<Rule> P, Set<Rule> R, boolean allStrict,
            Abortion aborter) {
        // * specialize interpretation based on assignment
        final int size = this.interpretation.size();
        Map<FunctionSymbol, OpVarPolynomial> solution = new HashMap<FunctionSymbol, OpVarPolynomial>(size);
        Map<String, BigInteger> mapToZero = new DefaultValueMap<String, BigInteger>(BigInteger.ZERO);
        for (Entry<FunctionSymbol, OpVarPolynomial> fAndInter : this.interpretation.entrySet()) {
            FunctionSymbol f = fAndInter.getKey();
            OpVarPolynomial oldInter = fAndInter.getValue();
            OpVarPolynomial newInter = oldInter.specialize(assignment);
            newInter = newInter.specialize(mapToZero);
            if (Globals.useAssertions) {
                assert newInter.isConcrete();
            }
            solution.put(f, newInter);
        }

        NonMonPoloInterpretation solutionInterpretation;
        solutionInterpretation = new NonMonPoloInterpretation(solution);

        // * remember which TermPairs have been oriented in what way,
        //   dealing with active (usable rule wrt the implicit AFS)
        //   in the process
        //   => The resulting order can at least deal with the constraints used
        //      for the search, which is just about enough :-)
        Map<TermPair, OrderRelation> knownInRel = new HashMap<TermPair, OrderRelation>(P.size()+R.size());

        // * find out which of the searchstrict coeffs have taken value 1 and
        //   thus which corresponding pairs from P have been oriented strictly
        if (allStrict) {
            for (Rule pRule : P) {
                TermPair tp = TermPair.create(pRule.getLhsInStandardRepresentation(),
                        pRule.getRhsInStandardRepresentation());
                knownInRel.put(tp, OrderRelation.GR);
            }
        }
        else {
            for (Rule pRule : P) {
                String ruleCoeff = this.searchstrictCoeffs.get(pRule);
                BigInteger value = assignment.get(ruleCoeff);

                // TODO (value == null) might mean that the value assigned to ruleCoeff
                // has been left unspecified by the search algorithm; however, a bug is
                // more likely.
                if (Globals.useAssertions) {
                    assert (value.intValue() == 0 || value.intValue() == 1) : "Illegal value " + value + " for searchstrict coeff " + ruleCoeff + " of pair " + pRule;
                }
                OrderRelation rel;

                if (value.signum() == 0) { // non-strict orientation
                    rel = OrderRelation.GE;
                }
                else if (value.equals(BigInteger.ONE)) { // strict orientation
                    rel = OrderRelation.GR;
                }
                else {
                    throw new RuntimeException("Unexpected value " + value +
                            " for SearchStrict coeff " + ruleCoeff +
                            " for pair " + pRule + "!");
                }
                TermPair tp = TermPair.create(pRule.getLhsInStandardRepresentation(),
                        pRule.getRhsInStandardRepresentation());
                knownInRel.put(tp, rel);
            }
        }
        /*
        NonMonPOLO orderJustForActiveChecking = NonMonPOLO.create(solutionInterpretation,
                Collections.<TermPair, Relation>emptyMap(), aborter);

        for (Entry<Rule, QActiveCondition> ruleWithQAC : R.entrySet()) {
            Rule rule = ruleWithQAC.getKey();
            QActiveCondition qac = ruleWithQAC.getValue();
            if (orderJustForActiveChecking.checkQActiveCondition(qac)) {
                TermPair tp = TermPair.create(rule.getLhsInStandardRepresentation(),
                        rule.getRhsInStandardRepresentation());
                knownInRel.put(tp, this.getUsableRulesRelation());
            }
        }
        */
        return NonMonPOLO.create(solutionInterpretation, knownInRel, aborter);
    }

    /**
     * @param t
     * @return [t]_Pol
     */
    public OpVarPolynomial interpretTerm(TRSTerm t) {
        // have we already seen t?
        OpVarPolynomial result;
        if (this.useMemory) {
            result = this.memory.get(t);
            if (result != null) {
                return result;
            }
        }

        // apparently t has not been interpreted by this yet (or the
        // cached value has been cleared away).
        if (t.isVariable()) { // easy: Variable
            result = OpVarPolynomial.create(VarPolynomial.createVariable(((TRSVariable) t).getName()));
        }
        else { // FunctionApplication
            // compute the interpretations of the arguments of t ...
            TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            if (args.isEmpty()) {
                // fApp is a constant; they are assigned
                // non-negative values only
                result = this.getInterpretation(fApp.getRootSymbol());
            }
            else {
                // x_j |-> poly interpretation of t|_j

                int size = args.size();
                Map<String, OpVarPolynomial> substitution = new LinkedHashMap<String, OpVarPolynomial>(size);
                for (int i = 0; i < size; ++i) {
                    String argVar = NonMonPoloInterpretation.VAR_PREFIX + (i+1);
                    OpVarPolynomial argPoly = this.interpretTerm(args.get(i));
                    substitution.put(argVar, argPoly);
                }

                // ... then get the interpretation of the root symbol, ...
                FunctionSymbol f = fApp.getRootSymbol();
                OpVarPolynomial rootInter = this.getInterpretation(f);

                // ... plug the arg polys into the root poly, ...
                result = rootInter.substituteVarsWithOpVPs(substitution, this.hookVarGen);

                // ... and make sure that max(interPossiblyNegative, 0)
                // is returned
                // nah, this better be done in the /symbol/ interpretation
/*
                boolean interCanBecomeNegative = (! rootInter.allPositive());
                if (interCanBecomeNegative) {
                    OpApp maxApp = OpApp.createMax(interPossiblyNegative,
                            OpVarPolynomial.ZERO);

                    String maxHookVar = this.getNextHookVar();
                    VarPolynomial newHookPoly = VarPolynomial.createVariable(maxHookVar);
                    Map<String, OpApp> varsToMaxApps;
                    varsToMaxApps = Collections.singletonMap(maxHookVar, maxApp);
                    result = OpVarPolynomial.create(newHookPoly, varsToMaxApps);
                }
                else { // for symbols f that are not interpreted negatively,
                    // no explicit wrapping inside max(.,0) is necessary
                    result = interPossiblyNegative;
                }*/
            }
        }
        if (this.useMemory) {
            this.memory.put(t, result);
        }
        return result;
    }

    /**
     * TODO
     * Which shape of interpretation do we intend to use for the paper?
     *
     * Returns the (linear) interpretation for f.
     * Creates a new interpretation if necessary.
     * Each interpretation for a n-ary f is a polynomial in
     * the variables x_1 to x_n, where x_ is the common variable prefix.
     *
     * Side effect: Extends this by f also for other purposes (ic, dc).
     *
     * @param f
     * @return the interpretation for f.
     */
    public OpVarPolynomial getInterpretation(FunctionSymbol f) {
        OpVarPolynomial opVP = this.interpretation.get(f);
        if (opVP == null) {
            int n = f.getArity();

            boolean heuristicAllowsNegConst = this.interHeuristic.allowNegConst(f);

            // Will be set to true if an abstract coeff is chosen in such a way that
            // f_Pol >= 0 is not guaranteed by itself; then max(0, .) will be wrapped
            // around the interpretation to assert this property.
            boolean negativeInter = false;

            // start with the constant part ...
            String coeff = this.getNextCoeff();
            SimplePolynomial sp = SimplePolynomial.create(coeff);

            if (n > 0 && heuristicAllowsNegConst) {
                sp = sp.plus(this.negRangePoly);
                negativeInter = true;
            }
            else { // negative addends only make sense for non-constants
                this.ranges.put(coeff, this.posRange);
            }
            opVP = OpVarPolynomial.create(VarPolynomial.create(sp));

            // ... then carry on with the part of the interpretation of f
            // that contains variables
            for (int i = 0; i < n; ++i) {
                coeff = this.getNextCoeff();
                sp = SimplePolynomial.create(coeff);
                if (this.interHeuristic.allowNegCoeff(f, i)) {
                    sp = sp.plus(this.negRangePoly);
                    negativeInter = true;
                }
                else {
                    this.ranges.put(coeff, this.posRange);
                }
                VarPolynomial addend = VarPolynomial.createVariable(NonMonPoloInterpretation.VAR_PREFIX+(i+1)).times(sp);
                opVP = opVP.plus(addend);
            }

            // ... and now deal with the max and min parts
            Map<String, OpApp> interHookToArgs = new LinkedHashMap<String, OpApp>();
            VarPolynomial maxMinPart = VarPolynomial.ZERO;
            for (Pair<Integer, Integer> maxPositionPair : this.interHeuristic.getMaxCombinations(f)) {
                // args
                OpVarPolynomial arg1 = OpVarPolynomial.createVariable(NonMonPoloInterpretation.VAR_PREFIX + (maxPositionPair.x + 1));
                OpVarPolynomial arg2 = OpVarPolynomial.createVariable(NonMonPoloInterpretation.VAR_PREFIX + (maxPositionPair.y + 1));
                OpApp maxApp = OpApp.createMax(arg1, arg2);
                String hookVar = this.getNextHookVar();
                interHookToArgs.put(hookVar, maxApp);

                // and hookVar
                coeff = this.getNextCoeff();
                this.ranges.put(coeff, this.posRange);
                sp = SimplePolynomial.create(coeff);
                VarPolynomial addend = VarPolynomial.createVariable(hookVar).times(sp);
                maxMinPart = maxMinPart.plus(addend);
            }

            for (Pair<Integer, Integer> minPositionPair : this.interHeuristic.getMinCombinations(f)) {
                // args
                OpVarPolynomial arg1 = OpVarPolynomial.createVariable(NonMonPoloInterpretation.VAR_PREFIX + (minPositionPair.x + 1));
                OpVarPolynomial arg2 = OpVarPolynomial.createVariable(NonMonPoloInterpretation.VAR_PREFIX + (minPositionPair.y + 1));
                OpApp minApp = OpApp.createMin(arg1, arg2);
                String hookVar = this.getNextHookVar();
                interHookToArgs.put(hookVar, minApp);

                // and hookVar
                coeff = this.getNextCoeff();
                this.ranges.put(coeff, this.posRange);
                sp = SimplePolynomial.create(coeff);
                VarPolynomial addend = VarPolynomial.createVariable(hookVar).times(sp);
                maxMinPart = maxMinPart.plus(addend);
            }

            // join the two parts
            OpVarPolynomial maxMinPartOpVP = OpVarPolynomial.create(maxMinPart, interHookToArgs);
            opVP = opVP.plus(maxMinPartOpVP);

            // enforce f_Pol >= 0
            if (negativeInter) {
                // MiniSAT seems to like max(0,p) better than max(p,0).
                // This may be due to the asymmetry during case analysis:
                // max(q,r) leads to the cases q >= r and r >= q + 1.
                OpApp maxApp = OpApp.createMax(OpVarPolynomial.ZERO, opVP);
                String maxHookVar = this.getNextHookVar();
                VarPolynomial newHookPoly = VarPolynomial.createVariable(maxHookVar);
                Map<String, OpApp> varsToMaxApps;
                varsToMaxApps = Collections.singletonMap(maxHookVar, maxApp);
                opVP = OpVarPolynomial.create(newHookPoly, varsToMaxApps);
            }

            this.interpretation.put(f, opVP);
        }
        return opVP;
    }


    /**
     * Converts OpVPCs to VPCs (with which we can deal the same way as
     * for "classical" POLOs). If the result of the conversion is
     * satisfiable, then so is its input.
     *
     * @param opVPCs - to be converted to VPCs
     * @return VPCs whose solution implies a solution for opVPCs
     */
    private Set<VarPolyConstraint> opVPCsToVPCs(Collection<OpVPC> opVPCs) {
        VPSubstitutor substitutor = new VPSubstitutor();
        Set<CondVPC> condVPCs = new LinkedHashSet<CondVPC>();
        for (OpVPC opVPC : opVPCs) {
            Set<CondVPC> currentCondVPCs = opVPC.toCondVPCs(substitutor);
            condVPCs.addAll(currentCondVPCs);
        }

        Set<VarPolyConstraint> result;
        result = this.deconditionalizer.transform(condVPCs, this.ranges);
        return result;
    }

    private String getNextCoeff() {
        ++this.nextCoeff;
        return NonMonPoloInterpretation.COEFF_PREFIX + this.nextCoeff;
    }

    private String getNextSearchStrictCoeff() {
        ++this.nextCoeff;
        return NonMonPoloInterpretation.SEARCHSTRICT_PREFIX + this.nextCoeff;
    }

    private String getNextHookVar() {
        return this.hookVarGen.next();
    }


    /**
     * Do not modify the returned map!
     *
     * @return the encapsulated mapping [FunctionSymbol -> OpVarPolynomial],
     *  i.e., the max-min-polynomial interpretation
     */
    public Map<FunctionSymbol, OpVarPolynomial> getPol() {
        return this.interpretation;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * Exports the mapping from function symbols to polynomials with variables.
     *
     * @param eu the export util
     * @return the exported version of the interpretation
     */
    public String export(Export_Util eu) {
        StringBuilder result = new StringBuilder("Polynomial interpretation with max "+eu.cite(NonMonPoloInterpretation.citations)+":\n");

        int size = this.interpretation.size();
        List<String> rows = new ArrayList<String>(size);

        Map<FunctionSymbol, OpVarPolynomial> sortedPol; // for ordered display
        sortedPol = new TreeMap<FunctionSymbol, OpVarPolynomial>(this.interpretation);
        for (Map.Entry<FunctionSymbol, OpVarPolynomial> entry : sortedPol.entrySet()) {
            StringBuilder line = new StringBuilder("POL(");
            FunctionSymbol functionSymbol = entry.getKey();
            int arity = functionSymbol.getArity();

            StringBuilder functionWithVars = new StringBuilder(functionSymbol.export(eu));
            if (arity > 0) {
                functionWithVars.append("(");
                for (int i = 1; i <= arity; ++i) {
                    StringBuilder varBuf;
                    String var = NonMonPoloInterpretation.VAR_PREFIX + i;
                    String[] split = var.split("_", 2);
                    varBuf = new StringBuilder(split[0]);
                    if (split.length > 1) {
                        varBuf.append(eu.sub(split[1]));
                    }
                    functionWithVars.append(varBuf);
                    if (i < arity) {
                        functionWithVars.append(", ");
                    }
                }
                functionWithVars.append(")");
            }

            line.append(eu.bold(functionWithVars.toString()));
            line.append(") = ");

            OpVarPolynomial varPoly = entry.getValue();
            line.append(varPoly.export(eu));

            // nasty hack for equidistant lines in HTML (and hence the GUI)
            if (eu instanceof HTML_Util) {
                line.append("<sup>&nbsp;</sup> <sub>&nbsp;</sub>");
            }
            rows.add(line.toString());
        }

        result.append(eu.set(rows, Export_Util.RULES));
        return result.toString();
    }

    /**
     * @return the deconditionalizer
     */
    public CondVPCToVPCTransformer getDeconditionalizer() {
        return this.deconditionalizer;
    }
}
