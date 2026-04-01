package aprove.verification.complexity.CdtProblem;

import java.util.*;
import java.util.Map.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.complexity.CdtProblem.Utils.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.complexity.TruthValue.ComplexityYNM.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.xml.*;
import immutables.*;

/**
 * Complexity Dependency Tuples problem.
 *
 * FIXME: Add documentation. Always innermost (even if the original TRS
 * may have been parallel-innermost)
 *
 * FIXME: Cache UsableRulesCalculator?
 */
public class CdtProblem extends DefaultBasicObligation implements DOT_Able {

    private static class TupleComputeState {
        Map<Cdt, Rule> cdts;
        Set<FunctionSymbol> compoundSymbols;
        Set<FunctionSymbol> definedPSymbols;
        Set<FunctionSymbol> definedRSymbols;
        FreshNameGenerator fng;
    }

    /**
     * The tuples of this problem.
     */
    private final ImmutableSet<Cdt> cdts;

    private final ImmutableSet<FunctionSymbol> compoundSymbols;

    /* Cached information */
    private final ImmutableSet<FunctionSymbol> definedPSymbols;

    private final ImmutableSet<FunctionSymbol> definedRSymbols;
    private final BasicCdtGraph graph;

    /**
     * The nodes whose complexity may be assumed as known.
     */
    private final ImmutableSet<Cdt> K;
    /**
     * The rules of this CdtProblem. All variables must be prefixed with
     * {@link IcapAlgorithm#PREFIX_NOTCAP}
     */
    private final ImmutableRuleSet<Rule> rules;
    /**
     * The nodes whose complexity still has to be computed.
     */
    private final ImmutableSet<Cdt> S;

    private final ImmutableSet<FunctionSymbol> signature;

    /**
     * @param rules See {@link #rules} for constraints.
     */
    private CdtProblem(
        final ImmutableRuleSet<Rule> rules,
        final ImmutableSet<Cdt> cdts,
        final ImmutableSet<Cdt> S,
        final ImmutableSet<Cdt> K,
        final BasicCdtGraph graph,
        final ImmutableSet<FunctionSymbol> compoundSymbols,
        final ImmutableSet<FunctionSymbol> definedRSymbols,
        final ImmutableSet<FunctionSymbol> definedPSymbols)
    {
        super("CdtProblem", "Complexity Dependency Tuples Problem");
        this.compoundSymbols = compoundSymbols;
        this.definedRSymbols = definedRSymbols;
        this.definedPSymbols = definedPSymbols;
        this.rules = rules;
        this.graph = graph;
        this.cdts = cdts;
        this.S = S;
        this.K = K;

        if (Globals.useAssertions) {
            assert (this.cdts.containsAll(this.S));
        }
        final LinkedHashSet<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>();
        signature.addAll(definedRSymbols);
        signature.addAll(CollectionUtils.getFunctionSymbols(rules));
        signature.addAll(CollectionUtils.getFunctionSymbols(cdts));
        this.signature = ImmutableCreator.create(signature);
    }

    /**
     * Computes CDTS
     */
    public static TupleComputeState computeTuples(
        final ImmutableSet<Rule> rules,
        final Set<FunctionSymbol> definedRSymbols)
    {
        return computeTuples(rules, definedRSymbols, false);
    }

    /**
     * Computes the information for the initial CDTProblem.
     *
     * @param rules  the rules for which we want to generate the initial
     *  CDTProblem
     * @param definedRSymbols  the symbols to be considered as defined
     *  symbols in the computation
     * @param parallelRewriting  true: compute CDTs for parallel-innermost
     *  rewriting (one or more per rule); false: compute CDTs for standard
     *  innermost rewriting (exactly one per rule)
     * @return the resulting TupleComputeState
     */
    public static TupleComputeState computeTuples(
        final ImmutableSet<Rule> rules,
        final Set<FunctionSymbol> definedRSymbols,
        boolean parallelRewriting)
    {
        final TupleComputeState state = new TupleComputeState();
        state.compoundSymbols = new LinkedHashSet<FunctionSymbol>(rules.size());
        state.definedRSymbols = java.util.Collections.unmodifiableSet(definedRSymbols);
        state.definedPSymbols = new LinkedHashSet<FunctionSymbol>(state.definedRSymbols.size());
        state.cdts = new LinkedHashMap<>(rules.size());
        state.fng = new FreshNameGenerator(CollectionUtils.getFunctionSymbols(rules), FreshNameGenerator.DEPENDENCY_PAIRS);

        for (final Rule rule : rules) {
            final TupleDefinedPositions tdps = TupleDefinedPositions.createFromRule(rule, state.definedRSymbols);
            List<Cdt> cdts = parallelRewriting
                    ? Cdt.createForParallelFromRule(state.fng, rule, tdps)
                    : Collections.singletonList(Cdt.createFromRule(state.fng, rule, tdps));
            for (Cdt cdt : cdts) {
                state.definedPSymbols.add(cdt.getRuleLHS().getRootSymbol());
                state.compoundSymbols.add(cdt.getCompoundSym());
                state.cdts.put(cdt, rule);
            }
        }

        return state;
    }

    public static Pair<Map<Cdt, Rule>, CdtProblem> create(final Set<Rule> rules) {
        return CdtProblem.create(rules, false);
    }

    public static Pair<Map<Cdt, Rule>, CdtProblem> create(
        final Set<Rule> rules,
        final boolean parallelRewriting)
    {
        return CdtProblem.create(rules, CollectionUtils.getRootSymbols(rules), parallelRewriting);
    }

    public static Pair<Map<Cdt, Rule>, CdtProblem> create(
        final Set<Rule> rules,
        final Set<FunctionSymbol> definedRSymbols)
    {
        return CdtProblem.create(rules, definedRSymbols, false);
    }

    public static Pair<Map<Cdt, Rule>, CdtProblem> create(
        final Set<Rule> rules,
        final Set<FunctionSymbol> definedRSymbols,
        final boolean parallelRewriting)
    {
        return CdtProblem.create(rules, definedRSymbols, null, parallelRewriting);
    }

    /**
     *
     * @param rules
     * @param definedRSymbols
     * @param relativeRules Rules that do not need to be counted in resulting problem, or null if all rules need to be counted.
     * @return
     */
    public static Pair<Map<Cdt, Rule>, CdtProblem> create(
        final Set<Rule> rules,
        final Set<FunctionSymbol> definedRSymbols,
        final Set<Rule> relativeRules)
    {
        return CdtProblem.create(rules, definedRSymbols, relativeRules, false);
    }

    /**
     *
     * @param rules
     * @param definedRSymbols
     * @param relativeRules Rules that do not need to be counted in resulting problem, or null if all rules need to be counted.
     * @param parallelRewriting true: generate initial problem for
     *  parallel-innermost rewriting; false: generate initial problem for
     *  standard innermost rewriting
     * @return
     */
    public static Pair<Map<Cdt, Rule>, CdtProblem> create(
        final Set<Rule> rules,
        final Set<FunctionSymbol> definedRSymbols,
        final Set<Rule> relativeRules,
        final boolean parallelRewriting)
    {
        final ImmutableRuleSet<Rule> renRules = new ImmutableRuleSet<Rule>(IcapAlgorithm.renumberedRules(rules));
        final TupleComputeState state = CdtProblem.computeTuples(renRules, definedRSymbols, parallelRewriting);

        final ImmutableSet<Cdt> cdts = ImmutableCreator.create(state.cdts.keySet());
        ImmutableSet<Cdt> s = cdts; // S in the CDT sense, not in the CpxRelTrs sense
        if (relativeRules != null) {
            if (Globals.useAssertions) {
                assert rules.containsAll(relativeRules);
            }
            final Set<Cdt> s_mut = new LinkedHashSet<>();
            for (final Entry<Cdt, Rule> c : state.cdts.entrySet()) {
                if (! relativeRules.contains(c.getValue())) {
                    s_mut.add(c.getKey());
                }
            }
            s = ImmutableCreator.create(s_mut);
        }
        return new Pair<>(state.cdts, new CdtProblem(
            renRules,
            cdts,
            s,
            ImmutableCreator.create(java.util.Collections.<Cdt>emptySet()),
            BasicCdtGraph.create(state.cdts.keySet(), renRules),
            ImmutableCreator.create(state.compoundSymbols),
            ImmutableCreator.create(state.definedRSymbols),
            ImmutableCreator.create(state.definedPSymbols)));
    }

    public static CdtProblem uncheckedCreate(
        final Set<Rule> rules,
        final Set<Cdt> cdts,
        final Set<FunctionSymbol> compoundSymbols,
        final Set<FunctionSymbol> definedRSymbols,
        final Set<FunctionSymbol> definedPSymbols)
    {
        return new CdtProblem(
            new ImmutableRuleSet<Rule>(rules),
            ImmutableCreator.create(cdts),
            ImmutableCreator.create(cdts),
            ImmutableCreator.create(java.util.Collections.<Cdt>emptySet()),
            BasicCdtGraph.create(cdts, rules),
            ImmutableCreator.create(compoundSymbols),
            ImmutableCreator.create(definedRSymbols),
            ImmutableCreator.create(definedPSymbols));
    }

    private static CdtProblem uncheckedCreate(
        final ImmutableRuleSet<Rule> rules,
        final BasicCdtGraph cdtGraph,
        final ImmutableSet<Cdt> S,
        final ImmutableSet<Cdt> K,
        final ImmutableSet<FunctionSymbol> definedRSymbols)
    {
        if (Globals.useAssertions) {
            assert (rules.equals(cdtGraph.getIcap().getRules()));
        }
        final ImmutableSet<Cdt> tuples = cdtGraph.getTuples();
        final Set<FunctionSymbol> compoundSymbols = new LinkedHashSet<FunctionSymbol>(tuples.size());
        final Set<FunctionSymbol> definedPSymbols = new LinkedHashSet<FunctionSymbol>();
        for (final Cdt tuple : tuples) {
            final TRSFunctionApplication right = tuple.getRuleRHS();
            compoundSymbols.add(right.getRootSymbol());
            definedPSymbols.add(tuple.getRule().getRootSymbol());
        }

        return new CdtProblem(
            rules,
            tuples,
            S,
            K,
            cdtGraph,
            ImmutableCreator.create(compoundSymbols),
            definedRSymbols,
            ImmutableCreator.create(definedPSymbols));
    }

    public CdtProblem createSubproblem(final BasicCdtGraph cdtGraph) {
        final LinkedHashSet<Cdt> newS = new LinkedHashSet<Cdt>(this.S);
        newS.retainAll(cdtGraph.getTuples());
        final LinkedHashSet<Cdt> newK = new LinkedHashSet<Cdt>(this.K);
        newK.retainAll(cdtGraph.getTuples());
        return this.createSubproblem(cdtGraph, ImmutableCreator.create(newS), ImmutableCreator.create(newK));
    }

    public CdtProblem createSubproblem(
        final BasicCdtGraph cdtGraph,
        final ImmutableSet<Cdt> S,
        final ImmutableSet<Cdt> K)
    {
        if (Globals.useAssertions) {
            assert (this.cdts.containsAll(cdtGraph.getTuples()));
        }
        return CdtProblem.uncheckedCreate(this.rules, cdtGraph, S, K, this.definedRSymbols);
    }

    /**
     * Creates a subproblem with a restricted set of rules.
     */
    public CdtProblem createSubproblem(final Set<Rule> rules) {
        if (Globals.useAssertions) {
            assert (this.getR().containsAll(rules));
        }
        final ImmutableRuleSet<Rule> iRules = new ImmutableRuleSet<Rule>(rules);
        /* We need to recompute the for two reasons:
         *   - If we have less rules, perhaps some of the edges do not exist
         *     anymore.
         *   - Some terms may be no longer normal and  hence we get
         *     additional edges
         */
        final BasicCdtGraph newGraph = BasicCdtGraph.create(this.graph.getTuples(), rules);
        final ImmutableSet<FunctionSymbol> definedRSymbols = ImmutableCreator.create(CollectionUtils.getRootSymbols(rules));
        return CdtProblem.uncheckedCreate(iRules, newGraph, this.S, this.K, definedRSymbols);
    }

    /**
     * Creates a new CDT problem for a complete transformation:
     *
     *   - Apply the map to the graph
     *   - Apply the map to S
     *   - Apply the map to K
     */
    public CdtProblem createTransformedComplete(
        final GraphHistory.Technique technique,
        final Map<Node<Cdt>, Set<Cdt>> transformations)
    {
        final BasicCdtGraph transGraph = this.graph.getTransformedGraph(technique, transformations);
        final ImmutableSet<Cdt> imTransformedS = this.getTransformedSet(this.S, transformations);
        final ImmutableSet<Cdt> imTransformedK = this.getTransformedSet(this.K, transformations);

        return CdtProblem.uncheckedCreate(this.rules, transGraph, imTransformedS, imTransformedK, this.definedRSymbols);
    }

    /**
     * Creates a new CDT problem for an incomplete transformation:
     *
     *   - Apply the map to the graph
     *   - Apply the map to S
     *   - Delete all nodes reachable from S from K
     */
    public CdtProblem createTransformedIncomplete(
        final GraphHistory.Technique technique,
        final Map<Node<Cdt>, Set<Cdt>> transformations)
    {
        final BasicCdtGraph transGraph = this.graph.getTransformedGraph(technique, transformations);
        final ImmutableSet<Cdt> imNewS = this.getTransformedSet(this.S, transformations);

        final Graph<Cdt, BitSet> basicGraph = this.graph.getGraph();
        final Set<Node<Cdt>> sNodes = basicGraph.getNodesFromObjects(this.S);
        final Set<Cdt> newK = new LinkedHashSet<Cdt>(this.K);
        newK.removeAll(basicGraph.determineReachableNodes(sNodes));
        final ImmutableSet<Cdt> imNewK = ImmutableCreator.create(newK);

        return CdtProblem.uncheckedCreate(this.rules, transGraph, imNewS, imNewK, this.definedRSymbols);
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        sb.append(o.escape("Complexity Dependency Tuples Problem"));
        sb.append(o.newline());
        sb.append(o.escape("Rules:"));
        sb.append(o.set(this.getR(), Export_Util.RULES));
        sb.append(o.escape("Tuples:"));
        sb.append(o.set(this.cdts, Export_Util.RULES));
        sb.append(o.escape("S tuples:"));
        sb.append(o.set(this.S, Export_Util.RULES));
        sb.append(o.escape("K tuples:"));
        sb.append(o.set(this.K, Export_Util.RULES));
        sb.append(o.escape("Defined Rule Symbols:"));
        sb.append(o.set(this.definedRSymbols, Export_Util.NICE_SET));
        sb.append(o.newline());
        sb.append(o.escape("Defined Pair Symbols:"));
        sb.append(o.set(this.definedPSymbols, Export_Util.NICE_SET));
        sb.append(o.newline());
        sb.append(o.escape("Compound Symbols:"));
        sb.append(o.set(this.compoundSymbols, Export_Util.NICE_SET));
        sb.append(o.newline());
        return sb.toString();
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        final Set<Cdt> strictDTs = this.getS();
        final Set<Cdt> weakDTs = new HashSet<>(this.getTuples());
        weakDTs.removeAll(strictDTs);
        final Element relative = CPFTag.RULES.create(doc);
        for (final Cdt cdt : weakDTs) {
            relative.appendChild(cdt.toCPF(doc, xmlMetaData));
        }
        for (final Rule rule : this.getR()) {
            relative.appendChild(rule.toCPF(doc, xmlMetaData));
        }
        final Element trs = CPFTag.RULES.create(doc);
        for (final Cdt cdt : strictDTs) {
            trs.appendChild(cdt.toCPF(doc, xmlMetaData));
        }
        final Element trsInput = CPFTag.TRS_INPUT.create(doc, CPFTag.TRS.create(doc, trs));
        if (this.isInnermost()) {
            trsInput.appendChild(CPFTag.STRATEGY.create(doc, CPFTag.INNERMOST.create(doc)));
        }
        trsInput.appendChild(CPFTag.RELATIVE_RULES.create(doc, relative));
        final Set<FunctionSymbol> defined = this.getTupleSymbols();
        final Set<FunctionSymbol> constructors = new HashSet<>(this.getSignature());
        constructors.removeAll(defined);
        constructors.removeAll(this.getDefinedRSymbols());
        constructors.removeAll(this.getCompoundSymbols());
        final Element cm =
            CPFTag.RUNTIME_COMPLEXITY.create(
                doc,
                FunctionSymbol.cpfSignature(doc, xmlMetaData, constructors),
                FunctionSymbol.cpfSignature(doc, xmlMetaData, defined));
        int deg;
        try {
            deg = ComplexityYNM.degreeOfUpperBound(tv);
        } catch (NoPolynomialUpperBoundException e) {
            return CPFTag.UNKNOWN_PROOF.create(doc);
        }
        final Element cpx = CPFTag.POLYNOMIAL.create(doc, deg);
        final Element cpxInput = CPFTag.COMPLEXITY_INPUT.create(doc, trsInput, cm, cpx);
        return cpxInput;
    }

    @Override
    public Element getCPFAssumption(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final CPFModus modus,
        final TruthValue tv)
    {
        return CPFTag.COMPLEXITY_PROOF.create(
            doc,
            CPFTag.COMPLEXITY_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
    }

    public ImmutableSet<FunctionSymbol> getCompoundSymbols() {
        return this.compoundSymbols;
    }

    public ImmutableSet<FunctionSymbol> getDefinedPSymbols() {
        return this.definedPSymbols;
    }

    public ImmutableSet<FunctionSymbol> getDefinedRSymbols() {
        return this.definedRSymbols;
    }

    public BasicCdtGraph getGraph() {
        return this.graph;
    }

    public ImmutableSet<Cdt> getK() {
        return this.K;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        // TODO Auto-generated method stub
        return null;
    }

    public ImmutableRuleSet<Rule> getR() {
        return this.rules;
    }

    public ImmutableSet<Cdt> getS() {
        return this.S;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#getStrategyName()
     */
    @Override
    public String getStrategyName() {
        return "cdt";
    }

    public ImmutableSet<Cdt> getTuples() {
        return this.cdts;
    }

    public Set<FunctionSymbol> getTupleSymbols() {
        final Set<FunctionSymbol> result = new LinkedHashSet<FunctionSymbol>();
        for (final Cdt cdt : this.cdts) {
            result.add(cdt.getRuleLHS().getRootSymbol());
            for (final TRSFunctionApplication rhs : cdt.getRuleRHSArgs()) {
                result.add(rhs.getRootSymbol());
            }
        }
        return result;
    }

    public UsableRulesCalculator getURCalc() {
        return this.getGraph().getIcap().getURCalc();
    }

    public boolean isInnermost() {
        return true;
    }

    /**
     * @return true if this has no lhs root symbol (from D or R) below the
     *  root of a lhs in D or R; false otherwise
     */
    public boolean isConstructorSystem() {
        Set<FunctionSymbol> lhsRoots = new LinkedHashSet<>();
        lhsRoots.addAll(this.getDefinedRSymbols());
        lhsRoots.addAll(this.getDefinedPSymbols());
        Set<FunctionSymbol> lhsArgSyms = new LinkedHashSet<>();
        collectLHSArgSyms(this.getR(), lhsArgSyms);
        collectLHSArgSyms(this.getTuples(), lhsArgSyms);
        boolean res = Collections.disjoint(lhsRoots, lhsArgSyms);
        return res;
    }

    private static void collectLHSArgSyms(Set<? extends HasLHS> hasLhss, Set<FunctionSymbol> lhsArgSyms) {
        for (HasLHS hasLhs : hasLhss) {
            TRSFunctionApplication lhs = hasLhs.getLeft();
            Collection<TRSTerm> args = lhs.getArguments();
            for (TRSTerm t : args) {
                lhsArgSyms.addAll(t.getFunctionSymbols());
            }
        }
    }

    public CdtProblem setS(final ImmutableSet<Cdt> tuples) {
        return new CdtProblem(
            this.getR(),
            this.getTuples(),
            tuples,
            this.getK(),
            this.getGraph(),
            this.getCompoundSymbols(),
            this.getDefinedPSymbols(),
            this.getDefinedRSymbols());
    }

    @Override
    public String toDOT() {
        return this.graph.toDOT();
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("Complexity Dependency Tuples Problem\n");
        sb.append("Rules:\n");
        for (final Rule rule : this.getR()) {
            sb.append(rule.toString());
            sb.append("\n");
        }
        sb.append("Tuples:\n");
        for (final Cdt cdt : this.cdts) {
            sb.append(cdt.toString());
            sb.append("\n");
        }
        sb.append("S tuples:\n");
        for (final Cdt cdt : this.S) {
            sb.append(cdt.toString());
            sb.append("\n");
        }
        sb.append("K tuples:\n");
        for (final Cdt cdt : this.K) {
            sb.append(cdt.toString());
            sb.append("\n");
        }
        sb.append("Defined Rule Symbols:\n");
        boolean first = true;
        for (final FunctionSymbol sym : this.definedRSymbols) {
            if (first) {
                first = false;
            } else {
                sb.append(", ");
            }
            sb.append(sym.toString());
        }
        sb.append("\n");
        sb.append("Defined Pair Symbols:\n");
        first = true;
        for (final FunctionSymbol sym : this.definedPSymbols) {
            if (first) {
                first = false;
            } else {
                sb.append(", ");
            }
            sb.append(sym.toString());
        }
        sb.append("\n");
        sb.append("Compound Symbols:\n");
        first = true;
        for (final FunctionSymbol sym : this.definedPSymbols) {
            if (first) {
                first = false;
            } else {
                sb.append(", ");
            }
            sb.append(sym.toString());
        }
        sb.append("\n");
        return sb.toString();
    }

    private ImmutableSet<Cdt> getTransformedSet(final Set<Cdt> s, final Map<Node<Cdt>, Set<Cdt>> transformations) {
        final Set<Cdt> sForNewNodes = new LinkedHashSet<Cdt>();
        for (final Map.Entry<Node<Cdt>, Set<Cdt>> e : transformations.entrySet()) {
            final Node<Cdt> oldNode = e.getKey();
            final Set<Cdt> newNodes = e.getValue();
            if (s.contains(oldNode.getObject())) {
                sForNewNodes.addAll(newNodes);
            }
        }
        final LinkedHashSet<Cdt> transformed = new LinkedHashSet<Cdt>(s);
        for (final Node<Cdt> n : transformations.keySet()) {
            transformed.remove(n.getObject());
        }
        transformed.addAll(sForNewNodes);
        return ImmutableCreator.create(transformed);
    }

}
