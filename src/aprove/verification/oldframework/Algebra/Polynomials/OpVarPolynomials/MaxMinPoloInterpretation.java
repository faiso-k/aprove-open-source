package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.Algebra.Polynomials.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Finding "Polynomial" Orders where the underlying interpretation may also
 * contain expressions like max(..., ...) and min(..., ...).
 *
 * @author fuhs
 * @version $Id$
 */
public class MaxMinPoloInterpretation implements XMLObligationExportable {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.MaxMinPoloInterpretation");

    private static final Citation[] citations = {Citation.POLO, Citation.MAXPOLO};

    private static final String COEFF_PREFIX = "a_";
    private static final String ACTIVE_PREFIX = "b_";
    private static final String SEARCHSTRICT_PREFIX = "s_";

    // the following two constants must be distinct, and
    // not one of them may be a prefix of the other.
    public static final String VAR_PREFIX = TRSTerm.STANDARD_PREFIX + "_";
    public static final String HOOK_PREFIX = TRSTerm.SECOND_STANDARD_PREFIX + "_";

    private final Map<FunctionSymbol, OpVarPolynomial> interpretation; // the interpretation
    private final Map<FunctionSymbol, SimplePolynomial[]> activeCoeffPolys;

    private final IndexedNameGenerator hookVarGen; // for creating new hook vars for max(.,.) or min(.,.)

    private int nextCoeff; // for new indefinite coeffs

    private final MMInterHeuristic interHeuristic;

    private final Map<GeneralizedRule, String> searchstrictCoeffs;

    private final Map<TRSTerm, OpVarPolynomial> memory; // (unbounded) caches for interpretation
    private final boolean useMemory;

    private final DefaultValueMap<String, BigInteger> ranges;

    private final SimplificationMode simplificationMode;
    private final boolean stripExponents;

    private final boolean useConstAddendInOp;
    // use max(a + x_i, b + x_j) instead of just max(x_i, x_j)?
    // (same for min(..., ...))

    /**
     * for abstract polynomial interpretations
     *
     * @param posRange
     * @param negRange
     */
    private MaxMinPoloInterpretation(final BigInteger range, final MMInterHeuristic interHeuristic,
            final SimplificationMode simplificationMode, final boolean stripExponents,
            final boolean useConstAddendInOp) {
        this.interpretation = new LinkedHashMap<FunctionSymbol, OpVarPolynomial>();
        this.activeCoeffPolys = new HashMap<FunctionSymbol, SimplePolynomial[]>();
        this.interHeuristic = interHeuristic;
        this.simplificationMode = simplificationMode;
        this.stripExponents = stripExponents;
        this.useConstAddendInOp = useConstAddendInOp;
        this.searchstrictCoeffs = new HashMap<GeneralizedRule, String>();
        this.hookVarGen = new IndexedNameGenerator(MaxMinPoloInterpretation.HOOK_PREFIX);
        this.nextCoeff = 0;
        if (Globals.useAssertions) {
            assert range.signum() > 0;
        }
        this.ranges = new DefaultValueMap<String, BigInteger>(range);
        this.memory = new HashMap<TRSTerm, OpVarPolynomial>();
        this.useMemory = true;
    }

    /**
     * for resulting concrete interpretations
     *
     * @param inter
     */
    private MaxMinPoloInterpretation(final Map<FunctionSymbol, OpVarPolynomial> inter) {
        this.interpretation = inter;
        this.activeCoeffPolys = null;
        this.interHeuristic = null;
        this.searchstrictCoeffs = null;
        this.nextCoeff = 0;
        this.hookVarGen = new IndexedNameGenerator(MaxMinPoloInterpretation.HOOK_PREFIX);
        this.ranges = null;
        this.memory = null;
        this.useMemory = false;
        this.simplificationMode = null;
        this.stripExponents = false;
        this.useConstAddendInOp = false;
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
    public static MaxMinPOLO solve(final Set<? extends GeneralizedRule> P, final Map<? extends GeneralizedRule, QActiveCondition> R,
            final BigInteger range, final boolean allStrict, final MMInterHeuristic interHeuristics,
            final SimplificationMode simplificationMode, final boolean stripExponents,
            final DiophantineSATConverter dioSatConv, final Engine engine,
            final boolean useConstAddendInOp,
            final Abortion aborter) throws AbortionException {
        if (Options.certifier.isCeta()) {
            return null; // CeTA does not support this order
        }
        long millisTotal1, millisTotal2;
        millisTotal1 = System.currentTimeMillis();
        final MaxMinPoloInterpretation inter = new MaxMinPoloInterpretation(range,
                interHeuristics, simplificationMode, stripExponents,
                useConstAddendInOp);
        final MaxMinPOLO result = inter.actuallySolve(P, R, allStrict, dioSatConv, engine, aborter);
        millisTotal2 = System.currentTimeMillis();
        if (MaxMinPoloInterpretation.log.isLoggable(Level.FINE)) {
            MaxMinPoloInterpretation.log.fine("The search for a MaxMinPOLO took " +
                    (millisTotal2 - millisTotal1) + " ms in total.\n");
        }
        return result;
    }


    private MaxMinPOLO actuallySolve(final Set<? extends GeneralizedRule> P, final Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean allStrict,
            final DiophantineSATConverter dioSatConv, final Engine engine,
            final Abortion aborter) throws AbortionException {
        long millis1, millis2;

        // 1) Encode to OpVPCs and a SimplePoly (for strictness)
        if (P.size() == 1) {
            allStrict = true;
        }
        millis1 = System.currentTimeMillis();
        final Pair<Set<OpVPC>, Set<SimplePolyConstraint>> opVPCsAndSP = this.encodeToOpVPCs(P, R,
                allStrict, aborter);
        millis2 = System.currentTimeMillis();

        if (MaxMinPoloInterpretation.log.isLoggable(Level.FINEST)) {
            MaxMinPoloInterpretation.log.finest("Interpretation of term constraints as OpVPCs took " + (millis2-millis1) + " ms.\n");
        }
        aborter.checkAbortion();

        // 2) OpVPCs (-> CondVPCs) -> VPCs
        millis1 = System.currentTimeMillis();
        final Set<VarPolyConstraint> vpcs = this.opVPCsToVPCs(opVPCsAndSP.x);
        millis2 = System.currentTimeMillis();
        if (MaxMinPoloInterpretation.log.isLoggable(Level.FINEST)) {
            MaxMinPoloInterpretation.log.finest("Conversion from " + opVPCsAndSP.x.size() +
                    " OpVPCs to " + vpcs.size() +" VPCs took " +
                    (millis2-millis1) + " ms.\n");
        }
        aborter.checkAbortion();

        // 3) VPCs -> SPCs (abs. positiveness);
        //    together with SimplePoly, get Diophantine problem for searchAlgorithm
        final Set<SimplePolyConstraint> spcs = new LinkedHashSet<SimplePolyConstraint>(3*vpcs.size());
        spcs.addAll(opVPCsAndSP.y);
        for (final VarPolyConstraint varPolyConstraint : vpcs) {
            Set<SimplePolyConstraint> absolutelyPositiveConstraints;
            absolutelyPositiveConstraints = varPolyConstraint.createCoefficientConstraints();
            spcs.addAll(absolutelyPositiveConstraints);
        }

        if (MaxMinPoloInterpretation.log.isLoggable(Level.FINEST)) {
            MaxMinPoloInterpretation.log.finest("About to encode " + spcs.size() + " constraints:\n");
            for (final SimplePolyConstraint spc : spcs) {
                MaxMinPoloInterpretation.log.log(Level.FINEST, spc + "\n");
            }
            MaxMinPoloInterpretation.log.finest("Ranges: " + this.ranges + "\n");
        }
        aborter.checkAbortion();

        // solve the diophantineProblem
        final DefaultValueMap<String, BigInteger> coeffRanges = this.ranges;

        SearchAlgorithm searchAlg;
        if (engine instanceof SatEngine) {
            final SatEngine satEngine = (SatEngine) engine;
            searchAlg = satEngine.getSearchAlgorithm(coeffRanges, dioSatConv);
        }
        else {
            searchAlg = engine.getSearchAlgorithm(coeffRanges);
        }

        searchAlg = SimplifyingSearch.create(searchAlg, true,
                this.stripExponents, this.simplificationMode);

        final Map<String, BigInteger> solution = searchAlg.search(spcs,
                Collections.<SimplePolyConstraint>emptySet(), aborter);

        MaxMinPOLO result;
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
    private MaxMinPOLO getSolution(final Map<String, BigInteger> assignment,
            final Set<? extends GeneralizedRule> P, final Map<? extends GeneralizedRule, QActiveCondition> R, final boolean allStrict,
            final Abortion aborter) {
        // * specialize interpretation based on assignment
        final Map<FunctionSymbol, OpVarPolynomial> solution = new LinkedHashMap<FunctionSymbol, OpVarPolynomial>(this.interpretation.size());
        for (final Entry<FunctionSymbol, OpVarPolynomial> fAndInter : this.interpretation.entrySet()) {
            final FunctionSymbol f = fAndInter.getKey();
            final OpVarPolynomial oldInter = fAndInter.getValue();
            OpVarPolynomial newInter = oldInter.specialize(assignment);
            newInter = newInter.specialize(new DefaultValueMap<String, BigInteger>(BigInteger.ZERO));
            /*
            if (Globals.useAssertions) {
                assert newInter.isConcrete();
            }
            */
            solution.put(f, newInter);
        }

        MaxMinPoloInterpretation solutionInterpretation;
        solutionInterpretation = new MaxMinPoloInterpretation(solution);

        // * remember which TermPairs have been oriented in what way,
        //   dealing with active (usable rule wrt the implicit AFS)
        //   in the process
        //   => The resulting order can at least deal with the constraints used
        //      for the search, which is just about enough :-)
        final Map<TermPair, OrderRelation> knownInRel = new HashMap<TermPair, OrderRelation>(P.size()+R.size());

        // * find out which of the searchstrict coeffs have taken value 1 and
        //   thus which corresponding pairs from P have been oriented strictly
        if (allStrict) {
            for (final GeneralizedRule pRule : P) {
                final TermPair tp = TermPair.create(pRule.getLhsInStandardRepresentation(),
                        pRule.getRhsInStandardRepresentation());
                knownInRel.put(tp, OrderRelation.GR);
            }
        }
        else {
            for (final GeneralizedRule pRule : P) {
                final String ruleCoeff = this.searchstrictCoeffs.get(pRule);
                final BigInteger value = assignment.get(ruleCoeff);

                // TODO (value == null) might mean that the value assigned to ruleCoeff
                // has been left unspecified by the search algorithm; however, a bug is
                // more likely.
                if (Globals.useAssertions) {
                    assert (value.signum() == 0 || value.equals(BigInteger.ONE)) : "Illegal value " + value + " for searchstrict coeff " + ruleCoeff + " of pair " + pRule;
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
                final TermPair tp = TermPair.create(pRule.getLhsInStandardRepresentation(),
                        pRule.getRhsInStandardRepresentation());
                knownInRel.put(tp, rel);
            }
        }
        final MaxMinPOLO orderJustForActiveChecking = MaxMinPOLO.create(solutionInterpretation,
                Collections.<TermPair, OrderRelation>emptyMap(), aborter);

        for (final Entry<? extends GeneralizedRule, QActiveCondition> ruleWithQAC : R.entrySet()) {
            final GeneralizedRule rule = ruleWithQAC.getKey();
            final QActiveCondition qac = ruleWithQAC.getValue();
            if (orderJustForActiveChecking.checkQActiveCondition(qac)) {
                final TermPair tp = TermPair.create(rule.getLhsInStandardRepresentation(),
                        rule.getRhsInStandardRepresentation());
                knownInRel.put(tp, OrderRelation.GE);
            }
        }

        return MaxMinPOLO.create(solutionInterpretation, knownInRel, aborter);
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

    public OpVarPolynomial interpretTerm(final TRSTerm t) {
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
            result = OpVarPolynomial.createVariable(((TRSVariable) t).getName());
        } else { // FunctionApplication
            // compute the interpretations of the arguments of t ...
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            final FunctionSymbol f = fApp.getRootSymbol();
            final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            final int size = args.size();
            if (size == 0) {
                // f is a constant (-> minor optimization, no substitution needed)
                result = this.getInterpretation(f);
            } else {
                // first interpret the args ...
                // x_j |-> poly interpretation of t|_j
                final Map<String, OpVarPolynomial> substitution = new LinkedHashMap<String, OpVarPolynomial>(size);
                for (int i = 0; i < size; ++i) {
                    final String argVar = MaxMinPoloInterpretation.VAR_PREFIX + (i+1);
                    final OpVarPolynomial argPoly = this.interpretTerm(args.get(i));
                    substitution.put(argVar, argPoly);
                }
                // ... then get the interpretation of the root symbol, ...
                final OpVarPolynomial rootInter = this.getInterpretation(f);
                // ... and plug the arg polys into the root poly
                result = rootInter.substituteVarsWithOpVPs(substitution, this.hookVarGen);
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
    private Pair<Set<OpVPC>, Set<SimplePolyConstraint>> encodeToOpVPCs(final Set<? extends GeneralizedRule> P,
            final Map<? extends GeneralizedRule, QActiveCondition> R, final boolean allStrict,
            final Abortion aborter) throws AbortionException {
        final Set<OpVPC> opVPCs = new LinkedHashSet<OpVPC>(P.size() + R.size());
        final Set<SimplePolyConstraint> sideConstraints = new LinkedHashSet<SimplePolyConstraint>(R.size()+1);

        SimplePolynomial sumOfSearchStrictCoeffs = (allStrict) ? null : SimplePolynomial.MINUS_ONE;
        for (final GeneralizedRule rule : P) {
            final OpVarPolynomial left = this.interpretTerm(rule.getLhsInStandardRepresentation());
            OpVarPolynomial right = this.interpretTerm(rule.getRhsInStandardRepresentation());
            if (allStrict) {
                right = right.plus(VarPolynomial.ONE);
            }
            else {
                final String searchStrictCoeff = this.getNextSearchStrictCoeff();
                final SimplePolynomial searchStrictSP = SimplePolynomial.create(searchStrictCoeff);
                right = right.plus(VarPolynomial.create(searchStrictSP));
                this.searchstrictCoeffs.put(rule, searchStrictCoeff);
                this.ranges.put(searchStrictCoeff, BigInteger.ONE);
                sumOfSearchStrictCoeffs = sumOfSearchStrictCoeffs.plus(searchStrictSP);
            }
            final OpVPC leftGEright = new OpVPC(left, right, ConstraintType.GE);
            opVPCs.add(leftGEright);
            aborter.checkAbortion();
        }
        if (! allStrict) {
            final SimplePolyConstraint searchStrictSpc = new SimplePolyConstraint(sumOfSearchStrictCoeffs,
                    ConstraintType.GE);
            sideConstraints.add(searchStrictSpc);
        }

        final Map<QActiveCondition, SimplePolynomial> qacCoeffCache = new HashMap<QActiveCondition, SimplePolynomial>();
        for (final Entry<? extends GeneralizedRule, QActiveCondition> e : R.entrySet()) {
            final GeneralizedRule rule = e.getKey();
            final QActiveCondition qac = e.getValue();
            OpVarPolynomial left = this.interpretTerm(rule.getLhsInStandardRepresentation());
            OpVarPolynomial right = this.interpretTerm(rule.getRhsInStandardRepresentation());

            final boolean isTrue = qac == QActiveCondition.TRUE;
            if (! isTrue) {
                final SimplePolynomial activeCond = this.getActiveCondition(qac,
                        sideConstraints, qacCoeffCache, aborter);
                left = left.times(activeCond);
                right = right.times(activeCond);
            }

            final OpVPC leftGEright = new OpVPC(left, right, ConstraintType.GE);
            opVPCs.add(leftGEright);
        }

        return new Pair<Set<OpVPC>, Set<SimplePolyConstraint>>(opVPCs, sideConstraints);
    }

    /**
     * @param qac - condition to be encoded
     * @param sideConstraints - must hold as well
     * @param cache - cache which maps active conditions to corresponding
     *  polynomials (used in order to avoid redundant coeffs)
     * @return a coefficient to be multiplied to this
     */
    private SimplePolynomial getActiveCondition(final QActiveCondition qac,
            final Set<SimplePolyConstraint> sideConstraints,
            final Map<QActiveCondition, SimplePolynomial> cache,
            final Abortion aborter) throws AbortionException {
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
        final String newActiveCoeff = MaxMinPoloInterpretation.ACTIVE_PREFIX+(this.nextCoeff++);
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
    public void addActiveConstraints(final Set<SimplePolyConstraint> constraints,
            final QActiveCondition condition, SimplePolynomial activeCondition,
            final Abortion aborter) throws AbortionException {
        activeCondition = activeCondition.plus(SimplePolynomial.MINUS_ONE);

        for (final Set<Pair<FunctionSymbol, Integer>> andCondition : condition.getSetRepresentation()) {
            aborter.checkAbortion();
            SimplePolynomial product = SimplePolynomial.ONE;
            for (final Pair<FunctionSymbol, Integer> pair : andCondition) {
                final SimplePolynomial[] activePolys = this.getActiveCoeffPolys(pair.x);
                final int position = pair.y.intValue();
                product = product.times(activePolys[position]);
            }
            constraints.add(new SimplePolyConstraint(activeCondition.times(product), ConstraintType.EQ));
        }
    }

    private SimplePolynomial[] getActiveCoeffPolys(final FunctionSymbol f) {
        SimplePolynomial[] result = this.activeCoeffPolys.get(f);
        if (result == null) {
            this.getInterpretation(f);
            // also initializes this.activeCoeffPolys for f

            result = this.activeCoeffPolys.get(f);
        }
        return result;
    }


    /**
     * Converts OpVPCs to VPCs (with which we can deal the same way as
     * for "classical" POLOs). If the result of the conversion is
     * satisfiable, then so is its input.
     *
     * @param opVPCs - to be converted to VPCs
     * @return VPCs
     */
    private Set<VarPolyConstraint> opVPCsToVPCs(final Collection<OpVPC> opVPCs) {
        final VPSubstitutor substitutor = new VPSubstitutor();
        final Set<CondVPC> condVPCs = new LinkedHashSet<CondVPC>();
        for (final OpVPC opVPC : opVPCs) {
            final Set<CondVPC> currentCondVPCs = opVPC.toCondVPCs(substitutor);
            condVPCs.addAll(currentCondVPCs);
        }

        final CondVPCToVPCTransformer deconditionalizer = new CondVPCToVPCTransformer();
        Set<VarPolyConstraint> result;
        result = deconditionalizer.transform(condVPCs, this.ranges);
        return result;
    }


    private String getNextCoeff() {
        ++this.nextCoeff;
        return MaxMinPoloInterpretation.COEFF_PREFIX + this.nextCoeff;
    }

    private String getNextSearchStrictCoeff() {
        ++this.nextCoeff;
        return MaxMinPoloInterpretation.SEARCHSTRICT_PREFIX + this.nextCoeff;
    }


    private String getNextHookVar() {
        return this.hookVarGen.next();
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
    public OpVarPolynomial getInterpretation(final FunctionSymbol f) {
        OpVarPolynomial opVP = this.interpretation.get(f);
        if (opVP == null) {
            final int n = f.getArity();

            // start with the constant part ...
            String coeff = this.getNextCoeff();
            SimplePolynomial sp = SimplePolynomial.create(coeff);
            VarPolynomial vp = VarPolynomial.create(sp);

            // ... then carry on with the part of the interpretation of f
            // that contains variables ...
            SimplePolynomial[] activeCoeffPolysForF;
            activeCoeffPolysForF = new SimplePolynomial[n];
            for (int i = 0; i < n; ++i) {
                coeff = this.getNextCoeff();
                sp = SimplePolynomial.create(coeff);
                final VarPolynomial addend = VarPolynomial.createVariable(MaxMinPoloInterpretation.VAR_PREFIX+(i+1)).times(sp);
                vp = vp.plus(addend);

                // store info for active:
                activeCoeffPolysForF[i] = sp;
            }

            // ... and now deal with the max and min parts
            final Map<String, OpApp> interHookToArgs = new LinkedHashMap<String, OpApp>();

            // debug
            /*boolean hasMaxMin = false;*/

            for (final Pair<Integer, Integer> maxPositionPair : this.interHeuristic.getMaxCombinations(f)) {
                // args
                OpVarPolynomial arg1 = OpVarPolynomial.createVariable(MaxMinPoloInterpretation.VAR_PREFIX + (maxPositionPair.x + 1));
                OpVarPolynomial arg2 = OpVarPolynomial.createVariable(MaxMinPoloInterpretation.VAR_PREFIX + (maxPositionPair.y + 1));

                if (this.useConstAddendInOp) {
                    // BEGIN hack for LPAR'08
                    // allow max(x_i + a, x_j + b) instead of just max(x_i, x_j)
                    arg1 = arg1.plus(VarPolynomial.createCoefficient(this.getNextCoeff()));
                    arg2 = arg2.plus(VarPolynomial.createCoefficient(this.getNextCoeff()));
                    // END hack for LPAR'08
                }

                final OpApp maxApp = OpApp.createMax(arg1, arg2);
                final String hookVar = this.getNextHookVar();
                interHookToArgs.put(hookVar, maxApp);

                // and hookVar
                coeff = this.getNextCoeff();
                sp = SimplePolynomial.create(coeff);
                final VarPolynomial addend = VarPolynomial.createVariable(hookVar).times(sp);
                vp = vp.plus(addend);

                // store info for active
                activeCoeffPolysForF[maxPositionPair.x] = activeCoeffPolysForF[maxPositionPair.x].plus(sp);
                activeCoeffPolysForF[maxPositionPair.y] = activeCoeffPolysForF[maxPositionPair.y].plus(sp);

/*                hasMaxMin = true;*/
            }

            for (final Pair<Integer, Integer> minPositionPair : this.interHeuristic.getMinCombinations(f)) {
                // args
                OpVarPolynomial arg1 = OpVarPolynomial.createVariable(MaxMinPoloInterpretation.VAR_PREFIX + (minPositionPair.x + 1));
                OpVarPolynomial arg2 = OpVarPolynomial.createVariable(MaxMinPoloInterpretation.VAR_PREFIX + (minPositionPair.y + 1));

                if (this.useConstAddendInOp) {
                    // analogous to max:
                    // allow min(x_i + a, x_j + b) instead of just min(x_i, x_j)
                    arg1 = arg1.plus(VarPolynomial.createCoefficient(this.getNextCoeff()));
                    arg2 = arg2.plus(VarPolynomial.createCoefficient(this.getNextCoeff()));
                }

                final OpApp minApp = OpApp.createMin(arg1, arg2);
                final String hookVar = this.getNextHookVar();
                interHookToArgs.put(hookVar, minApp);

                // and hookVar
                coeff = this.getNextCoeff();
                sp = SimplePolynomial.create(coeff);
                final VarPolynomial addend = VarPolynomial.createVariable(hookVar).times(sp);
                vp = vp.plus(addend);

                // store info for active
                activeCoeffPolysForF[minPositionPair.x] = activeCoeffPolysForF[minPositionPair.x].plus(sp);
                activeCoeffPolysForF[minPositionPair.y] = activeCoeffPolysForF[minPositionPair.y].plus(sp);

/*                hasMaxMin = true;*/
            }

            opVP = OpVarPolynomial.create(vp, interHookToArgs);
            /*
            if (hasMaxMin) {
                System.out.println("   --- Tried: " + f + " = " + opVP);
            }
            */
            this.interpretation.put(f, opVP);

            // store info for active
            this.activeCoeffPolys.put(f, activeCoeffPolysForF);
        }
        return opVP;
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
    public String export(final Export_Util eu) {
        final StringBuilder result = new StringBuilder("Polynomial interpretation with max and min functions "+eu.cite(MaxMinPoloInterpretation.citations)+":\n");

        final int size = this.interpretation.size();
        final List<String> rows = new ArrayList<String>(size);

        Map<FunctionSymbol, OpVarPolynomial> sortedPol; // for ordered display
        sortedPol = new TreeMap<FunctionSymbol, OpVarPolynomial>(this.interpretation);
        for (final Map.Entry<FunctionSymbol, OpVarPolynomial> entry : sortedPol.entrySet()) {
            final StringBuilder line = new StringBuilder("POL(");
            final FunctionSymbol functionSymbol = entry.getKey();
            final int arity = functionSymbol.getArity();

            final StringBuilder functionWithVars = new StringBuilder(functionSymbol.export(eu));
            if (arity > 0) {
                functionWithVars.append("(");
                for (int i = 1; i <= arity; ++i) {
                    StringBuilder varBuf;
                    final String var = MaxMinPoloInterpretation.VAR_PREFIX + i;
                    final String[] split = var.split("_", 2);
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
            line.append(entry.getValue().export(eu));

            // DEBUG
            /*
            if (! entry.getValue().isAtomic()) {
                System.out.println("   *** Found: " + entry.getKey() + " = " + entry.getValue());
            }*/

            // nasty hack for equidistant lines in HTML (and hence the GUI)
            if (eu instanceof HTML_Util) {
                line.append("<sup>&nbsp;</sup> <sub>&nbsp;</sub>");
            }
            rows.add(line.toString());
        }

        result.append(eu.set(rows, Export_Util.RULES));
        return result.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.POLO.createElement(doc);
        XMLAttribute.TYPE.setAttribute(e, "max");
        for (final Map.Entry<FunctionSymbol, OpVarPolynomial> entry : this.interpretation.entrySet()) {
            final Element poloInter = XMLTag.POLO_INTERPRETATION.createElement(doc);
            poloInter.appendChild(entry.getKey().toDOM(doc, xmlMetaData));
            poloInter.appendChild(entry.getValue().toDOM(doc, xmlMetaData));
            e.appendChild(poloInter);
        }
        return e;
    }

}
