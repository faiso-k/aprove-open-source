package aprove.verification.dpframework.Orders.SizeChangeNP;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SCNPOrder.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.PEncoders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Does the actual SAT encoding of SCNP.
 *
 * @author Carsten Fuhs
 */
public class SCNPFullEncoder {

    private final FormulaFactory<None> ff;

    // for comparing tags; maybe move to class LevelMapping
    private final ArithmeticCircuitFactory arithmeticFactory;

    private final SATPatterns<None> satPatterns;

    private final Formula<None> ZERO;
    private final Formula<None> ONE;

    // means of comparison for size changes in P
    private final boolean max;
    private final boolean min;
    private final boolean ms;
    private final boolean dms;

    private final boolean plain;
    private final boolean plainRoot;
    private final boolean rootArg;
    private final boolean listArgs;

    private final SCNPOrderEncoder orderEncoder; // for the base order
    private final LevelMappingEncoder levelMappingEncoder; // could also be a local variable
    private final Map<Comparison, Formula<None>> pComparisonEncodings;

    // avoid redundant constructions
    private final Map<TermPair, Formula<None>> knownGE;
    private final Map<TermPair, Formula<None>> knownGT;



    public SCNPFullEncoder(SolverFactory baseOrderFactory, SatEngine engine,
            boolean max, boolean min, boolean ms, boolean dms,
            boolean plain, boolean plainRoot, boolean rootArg, boolean listArgs,
            Set<? extends GeneralizedRule> P) {
        this.ff = engine.getFormulaFactory();
        this.arithmeticFactory = ArithmeticCircuitFactory.create(this.ff,
                new PoloSatConfigInfo());
        this.satPatterns = new SATPatterns<None>(this.ff);
        this.ZERO = this.ff.buildConstant(false);
        this.ONE = this.ff.buildConstant(true);

        this.max = max;
        this.min = min;
        this.ms = ms;
        this.dms = dms;
        this.plain = plain;
        this.plainRoot = plainRoot;
        this.rootArg = rootArg;
        this.listArgs = listArgs;

        this.orderEncoder = baseOrderFactory.getSCNPOrderEncoder(this.ff);
        this.levelMappingEncoder = new LevelMappingEncoder(plain, plainRoot, rootArg, listArgs, this.ff, this.arithmeticFactory, P);

        this.knownGE = new HashMap<TermPair, Formula<None>>();
        this.knownGT = new HashMap<TermPair, Formula<None>>();
        this.pComparisonEncodings = new LinkedHashMap<Comparison, Formula<None>>();
    }

    public Formula<None> encode(Set<? extends GeneralizedRule> P,
            Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean allstrict, Abortion aborter) throws AbortionException {

        /* Outline:
         * - TODO:
         *   encode that exactly one of the possible encodings for
         *   comparisons of argument tuples must be used
         *   (and remember for the proof output which formula stands
         *   for which comparison)
         *   - for each rule F(s_1, ..., s_k) -> G(t_1, ..., t_n) \in P:
         *     * for each s_i, t_j:
         *       - encode (s_i, tag^F_i) > (t_j, tag^G_j) and (s_i, tag^F_i) >= (t_j, tag^G_j)
         *         to SAT so that we can use this information as prop. formulas
         *         for the encoding of the ranking function for F, G
         *         (note that in general s_i > t_j does not imply s_i >= t_j)
         *
         * - for each allowed comparison c:
         *   - for each rule F(s_1, ..., s_k) -> G(t_1, ..., t_n) \in P:
         *     * encode the search for the tagged level mapping for F and G
         *       using comparison c to SAT, where we use the formulas for
         *       (s_i, tag^F_i) > (t_j, tag^G_j) computed in the previous step
         *
         *       Here we only make use of the abstract information of the
         *       relations between the s_i and t_j. Details on how to proceed
         *       here can be found in the TACAS'08 paper. We may omit
         *       "numerical" level mappings since those should be subsumed
         *       by the Dependency Graph processor, which one can apply at
         *       an earlier stage. "Plain" level mappings are a special case
         *       of "tagged" level mappings, but they can still be useful as
         *       an optional heuristic (just fix all tags to 0).
         *
         * - for each entry (l -> r, qac) in R:
         *   * encode l >= r
         *   * get the encoding for the atoms of qac that depend on the
         *     SCNPOrderEncoder (do this only /after/ all the rules have been
         *     handled since some information needed for the first qac could
         *     only have been generated while encoding a later )
         *   * encode the whole qac and add conjunct "qac -> l >= r"
         *     to overall formula
         *
         * In the process, make sure that the ranking function orients all
         * rules from P non-strictly and some rule from P strictly (if allstrict
         * is set, all rules from P must be oriented strictly).
         */

        List<Formula<None>> globalConjuncts = new ArrayList<Formula<None>>();
        Set<FunctionSymbol> baseSig = CollectionUtils.getFunctionSymbols(P);
        baseSig.addAll(CollectionUtils.getFunctionSymbols(R.keySet()));
        if (!this.rootArg) {baseSig.removeAll(CollectionUtils.getTupleSymbols(P, R.keySet()));}
        globalConjuncts.add(this.orderEncoder.pre(baseSig, aborter));

        Map<? extends GeneralizedRule, Pair<Formula<None>, Formula<None>>[][]> strictWeakArcsForP =
            this.encodeArcsForP(P, aborter);
        List<PRuleEncoder> pEncoders = new ArrayList<PRuleEncoder>();
        if (this.max) { pEncoders.add(new MaxRuleEncoder()); }
        if (this.min) { pEncoders.add(new MinRuleEncoder()); }
        if (this.ms ) { pEncoders.add(new MultisetRuleEncoder()); }
        if (this.dms) { pEncoders.add(new DualMultisetRuleEncoder()); }

        List<Formula<None>> pEncodings = new ArrayList<Formula<None>>();
        for (PRuleEncoder pEncoder : pEncoders) {
            Formula<None> capsule = this.ff.buildCapsule(pEncoder.encodeP(strictWeakArcsForP,
                    this.levelMappingEncoder, this.ff, this.satPatterns, allstrict, this.rootArg, aborter));
            pEncodings.add(capsule);
            this.pComparisonEncodings.put(pEncoder.getComparisonType(), capsule);
        }

        // There should be at least one!
        globalConjuncts.add(this.satPatterns.encodeSome(pEncodings));

        // usable rules matter, too
        globalConjuncts.add(this.encodeRWithQAC(R, aborter));

        globalConjuncts.add(this.orderEncoder.post(aborter));
        Formula<None> protoResult = this.ff.buildAnd(globalConjuncts);
        Formula<None> result = this.orderEncoder.toFinalFormula(protoResult, aborter);
        return result;
    }

    public SCNPOrder decode(int[] satModel, Abortion aborter)
                            throws AbortionException {
        Set<Integer> knownTrue = new LinkedHashSet<Integer>();
        for (int i : satModel) {
            if (i > 0) {
                knownTrue.add(i);
            }
        }

        LevelMapping levelMapping = this.levelMappingEncoder.decode(knownTrue);
        aborter.checkAbortion();

        Comparison comparison = null;
        for (Entry<Comparison, Formula<None>> e : this.pComparisonEncodings.entrySet()) {
            Formula<None> f = e.getValue();
            if (knownTrue.contains(f.getId())) {
                comparison = e.getKey();
                break;
            }
        }
        if (Globals.useAssertions) {
            assert comparison != null;
        }

        QActiveOrder argOrder = this.orderEncoder.decode(satModel, aborter);
        SCNPOrder res = new SCNPOrder(argOrder, levelMapping, comparison);
        return res;
    }


    /* comparisons of /arguments/ of P-rules (the size changes) */

    /**
     * For each rule of p, encodes the arcs in the respective local size change
     * graphs and returns them as a pair of strict and weak arcs for each pair
     * of top-level argument positions of a rule in p.
     *
     * @param p - size change constraints for all of them are to be encoded to SAT
     * @param aborter
     * @return map with entries (l -> r) |-> (||l > r||, ||l >= r||)
     * @throws AbortionException
     */
    private Map<? extends GeneralizedRule, Pair<Formula<None>, Formula<None>>[][]> encodeArcsForP(
            Set<? extends GeneralizedRule> p,
            Abortion aborter) throws AbortionException {
        // - encode all possible arcs between arguments
        Map<GeneralizedRule, Pair<Formula<None>, Formula<None>>[][]> ruleToStrictWeak =
            new LinkedHashMap<GeneralizedRule, Pair<Formula<None>, Formula<None>>[][]>(p.size());
        for (GeneralizedRule rule : p) {
            Pair<Formula<None>, Formula<None>>[][] arcsStrictWeak =
                this.encodeArcsForPRule(rule, aborter);
            ruleToStrictWeak.put(rule, arcsStrictWeak);
        }

        return ruleToStrictWeak;
    }

    /**
     * Encodes the arcs in the respective local size change graphs and
     * returns them as a pair of strict and weak arcs for each pair of
     * top-level argument positions of rule.
     *
     * @param rule - size change constraints for it are to be encoded to SAT
     * @param aborter
     * @return map with entries (l -> r) |-> (||l > r||, ||l >= r||)
     * @throws AbortionException
     */
    private Pair<Formula<None>, Formula<None>>[][] encodeArcsForPRule(GeneralizedRule rule,
            Abortion aborter) throws AbortionException {
        TRSFunctionApplication l = rule.getLeft();
        TRSFunctionApplication r = (TRSFunctionApplication)rule.getRight();
        ImmutableList<TRSTerm> lArgs = l.getArguments();
        ImmutableList<TRSTerm> rArgs = r.getArguments();
        int lArgsSize = lArgs.size() + (this.rootArg ? 1 : 0);
        int rArgsSize = rArgs.size() + (this.rootArg ? 1 : 0);

        FunctionSymbol lRoot = l.getRootSymbol();
        FunctionSymbol rRoot = r.getRootSymbol();

        List<List<Formula<None>>> lTags = this.levelMappingEncoder.getArgTagList(lRoot);
        List<List<Formula<None>>> rTags = this.levelMappingEncoder.getArgTagList(rRoot);

        Pair<Formula<None>, Formula<None>>[][] arcsStrictWeak =
            new Pair[lArgsSize][rArgsSize];

        aborter.checkAbortion();
        for (int j = 0; j < rArgsSize; ++j) {
            TRSTerm rArg = this.rootArg ? (j > 0 ? rArgs.get(j-1) : r) : rArgs.get(j);
            List<Formula<None>> rTag = rTags.get(j);
            for (int i = 0; i < lArgsSize; ++i) {
                TRSTerm lArg = this.rootArg ? (i > 0 ? lArgs.get(i-1) : l) : lArgs.get(i);
                List<Formula<None>> lTag = lTags.get(i);
                TermPair lrArgs = TermPair.create(lArg, rArg);
                Formula<None> strict = this.encodeTaggedGR(lrArgs, lTag, rTag, aborter);
                aborter.checkAbortion();
                Formula<None> weak   = this.encodeTaggedGE(lrArgs, lTag, rTag, aborter);
                aborter.checkAbortion();
                Pair<Formula<None>, Formula<None>> strictWeak =
                    new Pair<Formula<None>, Formula<None>>(strict, weak);
                arcsStrictWeak[i][j] = strictWeak;
            }
        }
        return arcsStrictWeak;
    }

    private Formula<None> encodeTaggedGE(TermPair lr, List<Formula<None>> lTag,
            List<Formula<None>> rTag, Abortion aborter) throws AbortionException {
        Formula<None> untaggedGR = this.encodeTermGR(lr, aborter);
        if (untaggedGR == this.ONE) { // success already!
            return this.ONE;
        }
        aborter.checkAbortion();
        Formula<None> untaggedGE = this.encodeTermGE(lr, aborter);
        // TODO is there any reduction pair in AProVE
        // where ">" in not a subset of ">="?
        Formula<None> result;
        if (this.plain) {
            result = this.ff.buildOr(untaggedGR, untaggedGE);
        }
        else {
            Formula<None> tagGE = this.arithmeticFactory.buildGECircuit(lTag, rTag).x;
            Formula<None> bothGE = this.ff.buildAnd(untaggedGE, tagGE);
            result = this.ff.buildOr(untaggedGR, bothGE);
        }
        return result;
    }

    /**
     * Encodes lr \in >= (i.e., l >= r). Uses known values and shortcuts.
     *
     * @param lr
     * @return SAT encoding of l >= r
     * @throws AbortionException
     */
    private Formula<None> encodeTermGE(TermPair lr, Abortion aborter) throws AbortionException {
        Formula<None> f = this.knownGE.get(lr);
        if (f != null) {
            return f;
        }
        TRSTerm l = lr.getLhsInStandardRepresentation();
        TRSTerm r = lr.getRhsInStandardRepresentation();
        if (l.isVariable() && r.isVariable()) {
            f = l.equals(r) ? this.ONE : this.ZERO;
            this.knownGE.put(lr, f);
            return f;
        }

        if (l.equals(r)) { // >= is reflexive
            this.knownGE.put(lr, this.ONE);
            return this.ONE;
        }

        // okay, we need to do some actual work
        Constraint<TRSTerm> c = Constraint.create(l, r, OrderRelation.GE);
        f = this.orderEncoder.encode(c, aborter);
        this.knownGE.put(lr, f);
        return f;
    }

    private Formula<None> encodeTaggedGR(TermPair lr, List<Formula<None>> lTag,
            List<Formula<None>> rTag, Abortion aborter) throws AbortionException {
        Formula<None> untaggedGR = this.encodeTermGR(lr, aborter);
        if (this.plain || untaggedGR == this.ONE) { // We're done already.
            return untaggedGR;
        }
        aborter.checkAbortion();
        Formula<None> untaggedGE = this.encodeTermGE(lr, aborter);
        Formula<None> tagGE = this.arithmeticFactory.buildGTCircuit(lTag, rTag);
        Formula<None> bothGE = this.ff.buildAnd(untaggedGE, tagGE);
        Formula<None> result = this.ff.buildOr(untaggedGR, bothGE);
        return result;
    }


    /**
     * Encodes lr \in > (i.e., l > r). Uses known values and shortcuts.
     *
     * @param lr
     * @return SAT encoding of l > r
     * @throws AbortionException
     */
    private Formula<None> encodeTermGR(TermPair lr, Abortion aborter) throws AbortionException {
        Formula<None> f = this.knownGT.get(lr);
        if (f != null) {
            return f;
        }
        TRSTerm l = lr.getLhsInStandardRepresentation();
        TRSTerm r = lr.getRhsInStandardRepresentation();
        if (l.isVariable() || l.equals(r)) {
            this.knownGT.put(lr, this.ZERO);
            return this.ZERO;
        }

        if (r.isVariable()) {
            TRSVariable v = (TRSVariable) r;
            Set<TRSVariable> lVars = l.getVariables();
            if (! lVars.contains(v)) {
                // l > v can only hold if l contains v
                // (otherwise consider l[v/l] == v[v/l])
                this.knownGT.put(lr, this.ZERO);
                return this.ZERO;
            }
        }

        // okay, we need to do some actual work
        Constraint<TRSTerm> c = Constraint.create(l, r, OrderRelation.GR);
        f = this.orderEncoder.encode(c, aborter);
        this.knownGT.put(lr, f);
        return f;
    }

    /* active */

    /**
     * Turns a QActiveCondition into its propositional equivalent.
     *
     * @param qac - to be encoded to prop. logic
     * @return a formula that expresses a sufficient condition for qac
     */
    private Formula<None> encodeQAC(QActiveCondition qac, Abortion aborter) throws AbortionException {
        if (qac == QActiveCondition.TRUE) {
            return this.ONE;
        }
        Set<? extends Set<Pair<FunctionSymbol, Integer>>> qDNF = qac.getSetRepresentation();
        List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(qDNF.size());
        for (Set<Pair<FunctionSymbol, Integer>> qDisjunct : qDNF) {
            List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(qDisjunct.size());
            for (Pair<FunctionSymbol, Integer> qAtom : qDisjunct) {
                Formula<None> proppedAtom =
                    this.encodeQActiveAtom(qAtom.x, qAtom.y, aborter);
                conjuncts.add(proppedAtom);
            }
            disjuncts.add(this.ff.buildAnd(conjuncts));
        }
        Formula<None> result = this.ff.buildOr(disjuncts);
        return result;
    }

    /**
     * @param f
     * @param i
     * @param aborter
     * @return a formula that is a sufficient condition for
     *  "f regards its i-th argument"
     */
    private Formula<None> encodeQActiveAtom(FunctionSymbol f, int i, Abortion aborter)
                                            throws AbortionException {
        if (this.levelMappingEncoder.knows(f)) {
            if (this.rootArg) {
                return this.ff.buildOr(this.levelMappingEncoder.getRegardedAt(f, i+1), this.orderEncoder.encodeQActiveAtom(f, i, aborter));
            }
            return this.levelMappingEncoder.getRegardedAt(f, i);
        }
        return this.orderEncoder.encodeQActiveAtom(f, i, aborter);
    }

    /**
     * @param rule - l -> r
     * @param qac
     * @param aborter
     * @return   || qac -> l >= r ||
     * @throws AbortionException
     */
    private Formula<None> encodeRRuleIfQAC(GeneralizedRule rule, QActiveCondition qac,
            Abortion aborter) throws AbortionException {
        TermPair lr = TermPair.create(rule.getLhsInStandardRepresentation(),
                rule.getRhsInStandardRepresentation());
        Formula<None> encodedRule = this.encodeTermGE(lr, aborter);
        Formula<None> encodedQAC = this.encodeQAC(qac, aborter);
        Formula<None> result = this.ff.buildImplication(encodedQAC, encodedRule);
        return result;
    }

    /**
     * @param rulesToQac
     * @param aborter
     * @return /\ || qac -> l >= r ||
     * @throws AbortionException
     */
    private Formula<None> encodeRWithQAC(Map<? extends GeneralizedRule, QActiveCondition> rulesToQac,
                    Abortion aborter) throws AbortionException {
        List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(rulesToQac.size());
        for (Entry<? extends GeneralizedRule, QActiveCondition> ruleIfQAC : rulesToQac.entrySet()) {
            aborter.checkAbortion();
            Formula<None> f = this.encodeRRuleIfQAC(ruleIfQAC.getKey(),
                    ruleIfQAC.getValue(), aborter);
            conjuncts.add(f);
        }
        Formula<None> result = this.ff.buildAnd(conjuncts);
        return result;
    }
}
