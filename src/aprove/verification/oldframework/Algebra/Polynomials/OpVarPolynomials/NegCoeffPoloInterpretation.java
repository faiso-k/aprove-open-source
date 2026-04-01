package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

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
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Finding Polynomial Orders with Negative Coefficients.
 *
 * @author fuhs
 * @version $Id$
 */
public class NegCoeffPoloInterpretation {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.NegCoeffPoloInterpretation");

    private static final Citation[] citations = {Citation.POLO, Citation.NEGPOLO};

    private static final String COEFF_PREFIX = "a_";
    private static final String ACTIVE_PREFIX = "b_";
    private static final String SEARCHSTRICT_PREFIX = "s_";

    // the following two constants must be distinct, and
    // not one of them may be a prefix of the other.
    public static final String VAR_PREFIX = TRSTerm.STANDARD_PREFIX + "_";
    public static final String HOOK_PREFIX = TRSTerm.SECOND_STANDARD_PREFIX + "_";

    protected final Map<FunctionSymbol, VarPolynomial> interpretation; // the interpretation
    private int nextCoeff; // for creating new coefficients
    private int nextHookVar; // for creating new hook variables for max(..., ...)

    protected final NCInterHeuristic interHeuristic;
    protected final SimplificationMode simplificationMode;
    protected final boolean stripExponents;

    private final boolean useEQforUsableRules;
    protected final BigInteger posRange;
    private final BigInteger negRange;
    protected final SimplePolynomial negRangePoly;

    private final Map<GeneralizedRule, String> searchstrictCoeffs;

    private final Map<TRSTerm, OpVarPolynomial> memory; // (unbounded) caches for interpretation
    private final boolean useMemory;

    protected final DefaultValueMap<String, BigInteger> ranges;

    /**
     * for abstract polynomial interpretations
     *
     * @param posRange
     * @param negRange
     */
    protected NegCoeffPoloInterpretation(BigInteger posRange, BigInteger negRange,
            NCInterHeuristic interHeuristic, SimplificationMode simplificationMode,
            boolean stripExponents, boolean useEQforUsableRules) {
        this.interpretation = new LinkedHashMap<FunctionSymbol, VarPolynomial>();
        this.interHeuristic = interHeuristic;
        this.simplificationMode = simplificationMode;
        this.stripExponents = stripExponents;
        this.searchstrictCoeffs = new HashMap<GeneralizedRule, String>();
        this.nextCoeff = 0;
        this.nextHookVar = 0;
        this.useEQforUsableRules = useEQforUsableRules;
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
    protected NegCoeffPoloInterpretation(Map<FunctionSymbol, VarPolynomial> inter,
            boolean useEQforUsableRules) {
        this.interpretation = inter;
        this.interHeuristic = null;
        this.searchstrictCoeffs = null;
        this.nextCoeff = 0;
        this.nextHookVar = 0;
        this.posRange = BigInteger.ONE; // irrelevant for concrete interpretations
        this.negRange = BigInteger.valueOf(-1l); // irrelevant for concrete interpretations
        this.negRangePoly = null;
        this.ranges = null;
        this.memory = null;
        this.useMemory = false;
        this.simplificationMode = null;
        this.stripExponents = false;
        this.useEQforUsableRules = useEQforUsableRules;
    }

    /**
     *
     * @param P
     * @param R
     * @param posRange
     * @param negRange
     * @param allStrict
     * @param interHeuristics
     * @param simplificationMode
     * @param stripExponents
     * @param dioSatConv
     * @param engine
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public static NegCoeffPOLO solve(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            BigInteger posRange, BigInteger negRange, boolean allStrict,
            NCInterHeuristic interHeuristics,
            SimplificationMode simplificationMode, boolean stripExponents,
            DiophantineSATConverter dioSatConv, Engine engine,
            boolean eqForUsableRules,
            Abortion aborter) throws AbortionException {
        long millisTotal1, millisTotal2;
        millisTotal1 = System.currentTimeMillis();
        NegCoeffPoloInterpretation inter = new NegCoeffPoloInterpretation(posRange, negRange,
                interHeuristics, simplificationMode, stripExponents, eqForUsableRules);
        NegCoeffPOLO result = inter.actuallySolve(P, R, allStrict, dioSatConv, engine, aborter);
        millisTotal2 = System.currentTimeMillis();
        if (NegCoeffPoloInterpretation.log.isLoggable(Level.FINE)) {
            NegCoeffPoloInterpretation.log.fine("The search for a POLO with negative coefficients took " +
                    (millisTotal2 - millisTotal1) + " ms in total.\n");
        }
        return result;
    }


    protected NegCoeffPOLO actuallySolve(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean allStrict,
            DiophantineSATConverter dioSatConv, Engine engine,
            Abortion aborter) throws AbortionException {
        long millis1, millis2;
        // 1) Encode to OpVPCs and a SimplePoly (for strictness)
        if (P.size() == 1) {
            allStrict = true;
        }
        millis1 = System.currentTimeMillis();
        Pair<Set<OpVPC>, Set<SimplePolyConstraint>> opVPCsAndSP = this.encodeToOpVPCs(P, R,
                allStrict, aborter);
        millis2 = System.currentTimeMillis();

        if (NegCoeffPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NegCoeffPoloInterpretation.log.finest("Interpretation of term constraints as OpVPCs took " + (millis2-millis1) + " ms.\n");
        }
        aborter.checkAbortion();

        // 2) OpVPCs (-> CondVPCs) -> VPCs
        millis1 = System.currentTimeMillis();
        Set<VarPolyConstraint> vpcs = this.opVPCsToVPCs(opVPCsAndSP.x);
        millis2 = System.currentTimeMillis();
        if (NegCoeffPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NegCoeffPoloInterpretation.log.finest("Conversion from " + opVPCsAndSP.x.size() +
                    " OpVPCs to " + vpcs.size() +" VPCs took " +
                    (millis2-millis1) + " ms.\n");
        }
        aborter.checkAbortion();

        // 3) VPCs -> SPCs (abs. positiveness);
        //    together with SimplePoly, get Diophantine problem for searchAlgorithm
        Set<SimplePolyConstraint> spcs = new LinkedHashSet<SimplePolyConstraint>(3*vpcs.size());
        spcs.addAll(opVPCsAndSP.y);
        for (VarPolyConstraint varPolyConstraint : vpcs) {
            Set<SimplePolyConstraint> absolutelyPositiveConstraints;
            absolutelyPositiveConstraints = varPolyConstraint.createCoefficientConstraints();
            spcs.addAll(absolutelyPositiveConstraints);
        }

        if (NegCoeffPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NegCoeffPoloInterpretation.log.finest("About to encode " + spcs.size() + " constraints:\n");
            for (SimplePolyConstraint spc : spcs) {
                NegCoeffPoloInterpretation.log.log(Level.FINEST, spc + "\n");
            }
            NegCoeffPoloInterpretation.log.finest("Ranges: " + this.ranges + "\n");
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
            searchAlg = engine.getSearchAlgorithm(coeffRanges);
        }

        searchAlg = SimplifyingSearch.create(searchAlg, true,
                this.stripExponents, this.simplificationMode);

        Map<String, BigInteger> solution = searchAlg.search(spcs,
                Collections.<SimplePolyConstraint>emptySet(), aborter);

        NegCoeffPOLO result;
        if (solution == null) {
            result = null;
        }
        else {
            result = this.getSolution(solution, P, R, allStrict, aborter);
        }
        return result;
    }

    /**
     * Converts a Diophantine model to the NegPolo ordering, i.e.,
     * specializes this based on the model.
     *
     * @param assignment
     * @return
     */
    protected NegCoeffPOLO getSolution(Map<String, BigInteger> assignment,
            Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R, boolean allStrict,
            Abortion aborter) {
        // * specialize interpretation based on assignment
        Map<FunctionSymbol, VarPolynomial> solution = new LinkedHashMap<FunctionSymbol, VarPolynomial>(this.interpretation.size());
        for (Entry<FunctionSymbol, VarPolynomial> fAndInter : this.interpretation.entrySet()) {
            FunctionSymbol f = fAndInter.getKey();
            VarPolynomial oldInter = fAndInter.getValue();
            VarPolynomial newInter = oldInter.specialize(assignment);
            newInter = newInter.specialize(new DefaultValueMap<String, BigInteger>(BigInteger.ZERO));
            if (Globals.useAssertions) {
                assert newInter.isConcrete();
            }
            solution.put(f, newInter);
        }

        NegCoeffPoloInterpretation solutionInterpretation;
        solutionInterpretation = new NegCoeffPoloInterpretation(solution,
                this.useEQforUsableRules);

        // * remember which TermPairs have been oriented in what way,
        //   dealing with active (usable rule wrt the implicit AFS)
        //   in the process
        //   => The resulting order can at least deal with the constraints used
        //      for the search, which is just about enough :-)
        Map<TermPair, OrderRelation> knownInRel = new HashMap<TermPair, OrderRelation>(P.size()+R.size());

        // * find out which of the searchstrict coeffs have taken value 1 and
        //   thus which corresponding pairs from P have been oriented strictly
        if (allStrict) {
            for (GeneralizedRule pRule : P) {
                TermPair tp = TermPair.create(pRule.getLhsInStandardRepresentation(),
                        pRule.getRhsInStandardRepresentation());
                knownInRel.put(tp, OrderRelation.GR);
            }
        }
        else {
            for (GeneralizedRule pRule : P) {
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

        NegCoeffPOLO orderJustForActiveChecking = NegCoeffPOLO.create(solutionInterpretation,
                Collections.<TermPair, OrderRelation>emptyMap(), aborter);

        for (Entry<? extends GeneralizedRule, QActiveCondition> ruleWithQAC : R.entrySet()) {
            GeneralizedRule rule = ruleWithQAC.getKey();
            QActiveCondition qac = ruleWithQAC.getValue();
            if (orderJustForActiveChecking.checkQActiveCondition(qac)) {
                TermPair tp = TermPair.create(rule.getLhsInStandardRepresentation(),
                        rule.getRhsInStandardRepresentation());
                knownInRel.put(tp, this.getUsableRulesRelation());
            }
        }

        return NegCoeffPOLO.create(solutionInterpretation, knownInRel, aborter);
    }

    /**
     *
     * @param qdp
     * @param coeffRange
     * @param constPosRange
     * @param constNegRange
     * @param aborter
     * @return a Pair of
     *  - the solving NegPolyOrder
     *  - set of rules of R that are still to be considered given the
     *    implicit AFS induced by the NegPolyOrder
     *  or null if no such NegPolyOrder could be found
     */
    /*
    public static Pair<NegPolyOrder, Set<Rule>> solve(QDPProblem qdp, int coeffRange,
            int constPosRange, int constNegRange, SATCheckerFactory factory,
            Abortion aborter) throws AbortionException {

        Set<Rule> P = qdp.getP();
        Map<Rule, QActiveCondition> R = qdp.getQUsableRulesCalculator().getActiveConditions(P);
        NegPolyOrder npo = solve(P, R, coeffRange, constPosRange, constNegRange, factory, aborter);

        Set<Rule> filteredR = new LinkedHashSet<Rule>(R.size());
        for (Map.Entry<Rule, QActiveCondition> e : R.entrySet()) {
            QActiveCondition cond = e.getValue();
            if (npo.checkQActiveCondition(cond)) {
                filteredR.add(e.getKey());
            }
        }
        return new Pair<NegPolyOrder, Set<Rule>>(npo, filteredR);
    }
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
        } else { // FunctionApplication
            // compute the interpretations of the arguments of t ...
            TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            if (args.isEmpty()) {
                // fApp is a constant; they are assigned
                // non-negative values only
                VarPolynomial vp = this.getInterpretation(fApp.getRootSymbol());
                result = OpVarPolynomial.create(vp);
            } else {
                // x_j |-> poly interpretation of t|_j
                int size = args.size();
                Map<String, OpVarPolynomial> substitution = new LinkedHashMap<String, OpVarPolynomial>(size);
                for (int i = 0; i < size; ++i) {
                    String argVar = NegCoeffPoloInterpretation.VAR_PREFIX + (i+1);
                    OpVarPolynomial argPoly = this.interpretTerm(args.get(i));
                    substitution.put(argVar, argPoly);
                }
                // ... then get the interpretation of the root symbol, ...
                FunctionSymbol f = fApp.getRootSymbol();
                VarPolynomial rootInter = this.getInterpretation(f);
                // ... plug the arg polys into the root poly, ...
                OpVarPolynomial interPossiblyNegative = rootInter.substituteVarsWithOpVPs(substitution);
                // ... and make sure that max(interPossiblyNegative, 0)
                // is returned
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
                }
            }
        }
        if (this.useMemory) {
            this.memory.put(t, result);
        }
        return result;
    }



    /**
     * encodes the (active) constraints that arise for the DP-Problem into a
     * Set of OpVPCs.
     *
     * @param P
     * @param R - usually the usable rules with active conditions
     * @param allStrict - true: orient all of P strictly
     *                   false: orient at least one of P strictly
     * @return
     *  x: the OpVPCs to be fulfilled
     *  y: additional side constraints to be fulfilled
     */
    protected Pair<Set<OpVPC>, Set<SimplePolyConstraint>> encodeToOpVPCs(Set<? extends GeneralizedRule> P,
            Map<? extends GeneralizedRule, QActiveCondition> R, boolean allStrict,
            Abortion aborter) throws AbortionException {
        Set<OpVPC> opVPCs = new LinkedHashSet<OpVPC>(P.size() + R.size());
        Set<SimplePolyConstraint> sideConstraints = new LinkedHashSet<SimplePolyConstraint>(R.size()+1);

        SimplePolynomial sumOfSearchStrictCoeffs = (allStrict) ? null : SimplePolynomial.MINUS_ONE;
        for (GeneralizedRule rule : P) {
            OpVarPolynomial left = this.interpretTerm(rule.getLhsInStandardRepresentation());
            OpVarPolynomial right = this.interpretTerm(rule.getRhsInStandardRepresentation());
            if (allStrict) {
                right = right.plus(VarPolynomial.ONE);
            }
            else {
                String searchStrictCoeff = this.getNextSearchStrictCoeff();
                SimplePolynomial searchStrictSP = SimplePolynomial.create(searchStrictCoeff);
                right = right.plus(VarPolynomial.create(searchStrictSP));
                this.searchstrictCoeffs.put(rule, searchStrictCoeff);
                this.ranges.put(searchStrictCoeff, BigInteger.ONE);
                sumOfSearchStrictCoeffs = sumOfSearchStrictCoeffs.plus(searchStrictSP);
            }
            OpVPC leftGEright = new OpVPC(left, right, ConstraintType.GE);
            opVPCs.add(leftGEright);
            aborter.checkAbortion();
        }
        if (! allStrict) {
            SimplePolyConstraint searchStrictSpc = new SimplePolyConstraint(sumOfSearchStrictCoeffs,
                    ConstraintType.GE);
            sideConstraints.add(searchStrictSpc);
        }

        Map<QActiveCondition, SimplePolynomial> qacCoeffCache = new HashMap<QActiveCondition, SimplePolynomial>();
        for (Entry<? extends GeneralizedRule, QActiveCondition> e : R.entrySet()) {
            GeneralizedRule rule = e.getKey();
            QActiveCondition qac = e.getValue();
            OpVarPolynomial left = this.interpretTerm(rule.getLhsInStandardRepresentation());
            OpVarPolynomial right = this.interpretTerm(rule.getRhsInStandardRepresentation());

            boolean isTrue = qac == QActiveCondition.TRUE;
            if (! isTrue) {
                SimplePolynomial activeCond = this.getActiveCondition(qac,
                        sideConstraints, qacCoeffCache, aborter);
                left = left.times(activeCond);
                right = right.times(activeCond);
            }

            OpVPC leftEQright = this.encodeLeftRightR(left, right);
            opVPCs.add(leftEQright);
        }

        return new Pair<Set<OpVPC>, Set<SimplePolyConstraint>>(opVPCs, sideConstraints);
    }

    /**
     * With negative coefficients also for variables, we need to restrict
     * ourselves to EQ constraints.
     * @param left - stands for the lhs of a rule of R
     * @param right - stands for the rhs of a rule of R
     * @return a corresponding VPC to be solved
     */
    protected OpVPC encodeLeftRightR(OpVarPolynomial left, OpVarPolynomial right) {
        return new OpVPC(left, right, ConstraintType.EQ);
    }

    /**
     * @return that usable rules must be oriented with EQ when using
     *  negative constants
     */
    protected OrderRelation getUsableRulesRelation() {
        return this.useEQforUsableRules ? OrderRelation.EQ : OrderRelation.GE;
    }

    /**
     * @param qac - condition to be encoded
     * @param sideConstraints - must hold as well
     * @param cache - cache which maps active conditions to corresponding
     *  polynomials (used in order to avoid redundant coeffs)
     * @return a coefficient to be multiplied to this
     */
    private SimplePolynomial getActiveCondition(QActiveCondition qac,
            Set<SimplePolyConstraint> sideConstraints,
            Map<QActiveCondition, SimplePolynomial> cache,
            Abortion aborter) throws AbortionException {
        SimplePolynomial activeCondition = cache.get(qac);

        // do we already have an active condition or do we need to create a new one?
        if (activeCondition == null) {
            // we need a new one

            // get fresh coefficient for active condition
            activeCondition = this.extendByActiveCondition();
            cache.put(qac, activeCondition);

            // if we have f/1^g/2 v h/3 then build "(activeCondition - 1) * f/1 * g/2 = 0" and
            // "(activeCondition - 1) * h/3 = 0"
            this.addActiveConstraints(sideConstraints, qac, activeCondition, aborter);
        }
        return activeCondition;
    }

    private SimplePolynomial extendByActiveCondition() {
        String newActiveCoeff = NegCoeffPoloInterpretation.ACTIVE_PREFIX+(this.nextCoeff++);
        this.ranges.put(newActiveCoeff, BigInteger.ONE);
        return SimplePolynomial.create(newActiveCoeff);
    }

    /**
     * Given an activation condition and the corresponding coefficient
     * "activeCondition", adds those constraints to the "constraints" set
     * such that the activeCondition = 1 is enforced if the activation
     * condition evaluates to true.
     *
     * @param constraints - we add the new constraints to this set
     * @param condition - this is the qactive condition
     * @param activeCondition - the coefficient which should store "condition is active"
     * @param aborter
     */
    public void addActiveConstraints(Set<SimplePolyConstraint> constraints,
            QActiveCondition condition, SimplePolynomial activeCondition,
            Abortion aborter) throws AbortionException {
        activeCondition = activeCondition.plus(SimplePolynomial.MINUS_ONE);

        for (Set<Pair<FunctionSymbol, Integer>> andCondition : condition.getSetRepresentation()) {
            aborter.checkAbortion();
            SimplePolynomial product = SimplePolynomial.ONE;
            for (Pair<FunctionSymbol, Integer> pair : andCondition) {
                VarPolynomial poly = this.getInterpretation(pair.x);
                int position = pair.y.intValue();
                String var = NegCoeffPoloInterpretation.VAR_PREFIX+(position+1);

                SimplePolynomial sumOfSquaredCoeffs = SimplePolynomial.ZERO;
                List<SimplePolynomial> coeffPolys = poly.getListOfCoefficientPolys(var);

                for (SimplePolynomial currentCoeffPoly : coeffPolys) {
                    // just using the sum is not okay if we may use neg addends,
                    // so square the addends before summing them up if necessary
                    if (! currentCoeffPoly.allPositive()) {
                        currentCoeffPoly = currentCoeffPoly.times(currentCoeffPoly);
                    }
                    sumOfSquaredCoeffs = sumOfSquaredCoeffs.plus(currentCoeffPoly);
                }
                product = product.times(sumOfSquaredCoeffs);
            }
            constraints.add(new SimplePolyConstraint(activeCondition.times(product), ConstraintType.EQ));
        }
    }


    /**
     * Converts OpVPCs to VPCs (with which we can deal the same way as
     * for "classical" POLOs). If the result of the conversion is
     * satisfiable, then so is its input.
     *
     * @param opVPCs - to be converted to VPCs
     * @return VPCs
     */
    protected Set<VarPolyConstraint> opVPCsToVPCs(Collection<OpVPC> opVPCs) {
        VPSubstitutor substitutor = new VPSubstitutor();
        Set<CondVPC> condVPCs = new LinkedHashSet<CondVPC>();
        for (OpVPC opVPC : opVPCs) {
            Set<CondVPC> currentCondVPCs = opVPC.toCondVPCs(substitutor);
            condVPCs.addAll(currentCondVPCs);
        }

        CondVPCToVPCTransformer deconditionalizer = new CondVPCToVPCTransformer();
        Set<VarPolyConstraint> result;
        result = deconditionalizer.transform(condVPCs, this.ranges);
        return result;
    }


    protected String getNextCoeff() {
        ++this.nextCoeff;
        return NegCoeffPoloInterpretation.COEFF_PREFIX + this.nextCoeff;
    }

    private String getNextSearchStrictCoeff() {
        ++this.nextCoeff;
        return NegCoeffPoloInterpretation.SEARCHSTRICT_PREFIX + this.nextCoeff;
    }


    private String getNextHookVar() {
        ++this.nextHookVar;
        return NegCoeffPoloInterpretation.HOOK_PREFIX + this.nextHookVar;
    }


    /**
     * Returns the (linear) interpretation for f.
     * Creates a new interpretation if necessary.
     * Each interpretation for a n-ary f is a polynomial in
     * the variables x_1 to x_n, where x_ is the common variable prefix.
     *
     * @param f
     * @return
     */
    public VarPolynomial getInterpretation(FunctionSymbol f) {
        VarPolynomial vp = this.interpretation.get(f);
        if (vp == null) {
            int n = f.getArity();
            boolean heuristicAllowsNegConst = this.interHeuristic.useNegConst(f);

            // start with the constant part ...
            String coeff = this.getNextCoeff();
            SimplePolynomial sp = SimplePolynomial.create(coeff);

            if (n > 0 && heuristicAllowsNegConst) {
                sp = sp.plus(this.negRangePoly);
            }
            else { // negative addends only make sense for non-constants
                this.ranges.put(coeff, this.posRange);
            }
            vp = VarPolynomial.create(sp);

            // ... then carry on with the part of the interpretation of f
            // that contains variables
            for (int i = 0; i < n; ++i) {
                boolean heuristicAllowsNegCoeff = this.interHeuristic.useNegCoeff(f, i);
                coeff = this.getNextCoeff();
                sp = SimplePolynomial.create(coeff);
                if (heuristicAllowsNegCoeff) {
                    sp = sp.plus(this.negRangePoly);
                }
                else {
                    this.ranges.put(coeff, this.posRange);
                }
                VarPolynomial addend = VarPolynomial.createVariable(NegCoeffPoloInterpretation.VAR_PREFIX+(i+1)).times(sp);
                vp = vp.plus(addend);
            }
            this.interpretation.put(f, vp);
        }
        return vp;
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
        StringBuilder result = new StringBuilder("Polynomial interpretation "+eu.cite(NegCoeffPoloInterpretation.citations)+":\n");

        int size = this.interpretation.size();
        List<String> rows = new ArrayList<String>(size);

        Map<FunctionSymbol, VarPolynomial> sortedPol; // for ordered display
        sortedPol = new TreeMap<FunctionSymbol, VarPolynomial>(this.interpretation);
        for (Map.Entry<FunctionSymbol, VarPolynomial> entry : sortedPol.entrySet()) {
            StringBuilder line = new StringBuilder("POL(");
            FunctionSymbol functionSymbol = entry.getKey();
            int arity = functionSymbol.getArity();

            StringBuilder functionWithVars = new StringBuilder(functionSymbol.export(eu));
            if (arity > 0) {
                functionWithVars.append("(");
                for (int i = 1; i <= arity; ++i) {
                    StringBuilder varBuf;
                    String var = NegCoeffPoloInterpretation.VAR_PREFIX + i;
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

            VarPolynomial varPoly = entry.getValue();
            if (varPoly.allPositive()) {
                line.append(varPoly.export(eu));
            }
            else {
                line.append(eu.export("max{0, "));
                line.append(varPoly.export(eu));
                line.append(eu.export("}"));
            }

            // nasty hack for equidistant lines in HTML (and hence the GUI)
            if (eu instanceof HTML_Util) {
                line.append("<sup>&nbsp;</sup> <sub>&nbsp;</sub>");
            }
            rows.add(line.toString());
        }

        result.append(eu.set(rows, Export_Util.RULES));
        return result.toString();
    }
}
