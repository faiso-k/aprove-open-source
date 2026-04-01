package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * The PrologToCdtProblemTransformer builds a derivation graph
 * and extracts CdtProblems from it for which an upper bound
 * guarantees this upper bound for the PrologProgram.
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologToCdtProblemTransformer extends PrologGraphProcessor {

    /**
     * Standard proof containing the constructed graph.
     * @author cryingshadow
     */
    public class PrologToCdtProblemTransformerProof extends PrologGraphProcessorProof {

        /**
         * Standard constructor.
         * @param petGraph The constructed graph.
         * @param exportGraph Flag whether the graph shall be exported
         *                    graphically.
         * @param exportLimit Limit on number of nodes for graphical export.
         * @param nodeLabels Mapping from node numbers to labels to keep the
         *                   connection between graph and rules.
         */
        public PrologToCdtProblemTransformerProof(
            final PrologEvaluationGraph petGraph,
            final boolean exportGraph,
            final int exportLimit,
            final Map<Integer, String> nodeLabels)
        {
            super(petGraph, exportGraph, exportLimit, nodeLabels);
        }

        @Override
        protected String getProofMessage() {
            //TODO add citation
            return "Built complexity over-approximating cdt problems from derivation graph.";
        }

    }

    /**
     * Standard logger...
     */
    private static final Logger log =
        Logger.getLogger("aprove.input.Programs.prolog.processors.PrologToCdtProblemTransformer");

    /**
     * Flag to switch the handling of multiplicative splits on (false) and off (true).
     */
    private static final boolean NO_MULTIPLICATIVE_SPLITS = false;

    /**
     * Standard constructor.
     * @param args The arguments of this processor.
     */
    @ParamsViaArgumentObject
    public PrologToCdtProblemTransformer(final PrologOptions args) {
        super(args);
        this.options.setComplexityHeuristic(true);
    }

    /**
     * The main method of this processor. It calculates a set of CdtProblems
     * from the specified graph and combines them according to multiplicative
     * SPLIT nodes.
     * @param graph The graph to consider.
     * @param nodeLabels Mapping from node numbers to labels.
     * @param aborter For abortions...
     * @return The obligation returned by this processor.
     * @throws AbortionException If it is aborted...
     */
    @SuppressWarnings("unused")
    public static BasicObligation calculateCdtProblemsFromGraph(
        final PrologEvaluationGraph graph,
        final Map<Integer, String> nodeLabels,
        final Abortion aborter
    ) throws AbortionException {
        final CpxNodeSets cpxSet = graph.getCpxNodeSetsForPaths(aborter);
        //        The following is not necessary as we only consider ground variables in TRSs.
        //        As soon as we lift this restriction, we also need to consider evil PARALLEL nodes!
        //        if (PrologToComplexityProblemTransformer.hasEvilParallel(graph, cpxSet, aborter)) {
        //            return null;
        //        }
        final Set<Node<PrologAbstractState>> multiplicativeSplits =
            PrologToComplexityProblemTransformer.calculateMultiplicativeSplits(graph, cpxSet, aborter);
        aborter.checkAbortion();
        if (PrologToCdtProblemTransformer.NO_MULTIPLICATIVE_SPLITS && !multiplicativeSplits.isEmpty()) {
            return null;
        }
        if (!PrologToCdtProblemTransformer.isDecomposable(graph, multiplicativeSplits)) {
            return null;
        }
        final Map<Node<PrologAbstractState>, Set<Node<PrologAbstractState>>> reachableMultis =
            PrologToCdtProblemTransformer.calculateReachableMultiplicativeSplits(graph, multiplicativeSplits, aborter);
        final List<Pair<Node<PrologAbstractState>, CpxNodeSets>> sets =
            new ArrayList<Pair<Node<PrologAbstractState>, CpxNodeSets>>();
        for (final Node<PrologAbstractState> node : reachableMultis.keySet()) {
            sets.add(new Pair<Node<PrologAbstractState>, CpxNodeSets>(node, PrologToCdtProblemTransformer
                .getCpxNodeSetsForPathsFromNode(graph, cpxSet, node, multiplicativeSplits)));
        }
        final Set<String> used = new LinkedHashSet<String>();
        used.add("U");
        used.add("X");
        used.add("f");
        final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_FUNCS);
        final GroundnessAnalysis ground = AbstractGraphBuilderHeuristic.generateGroundnessAnalysis(graph);
        final Map<Node<PrologAbstractState>, CdtProblem> cdtProblems = new LinkedHashMap<Node<PrologAbstractState>, CdtProblem>();
        for (
            Pair<Node<PrologAbstractState>, Set<List<Node<PrologAbstractState>>>> pathSetPair :
                PrologToComplexityProblemTransformer.calculateAllConnectionPaths(
                    graph,
                    sets,
                    multiplicativeSplits,
                    aborter
                )
        ) {
            final Set<Rule> rules = new LinkedHashSet<Rule>();
            for (final List<Node<PrologAbstractState>> path : pathSetPair.y) {
                rules.addAll(RuleConstructor.buildConnectionRules(path, graph, ground, fridge, aborter));
            }
            for (final Node<PrologAbstractState> split : cpxSet.getSplitNodes()) {
                rules.addAll(RuleConstructor.buildSplitRules(split, graph, ground, true, fridge, aborter));
            }
            // Rules for PARALLEL nodes are necessary since PARALLEL nodes reaching themselves can lead to exponential
            // runtime!
            for (final Node<PrologAbstractState> parallel : cpxSet.getParallelNodes()) {
                rules.addAll(RuleConstructor.buildParallelRules(parallel, graph, ground, fridge, aborter));
            }
            cdtProblems.put(pathSetPair.x, CdtProblem.create(rules).y);
        }
        return PrologToCdtProblemTransformer.combineToComplexProblem(graph, cdtProblems, reachableMultis);
    }

    /**
     * Computes the relevant nodes reachable from the specified node without
     * traversing multiplicative SPLITs.
     * @param graph The graph to consider.
     * @param sets The relevant nodes for the whole graph.
     * @param node The start node to consider.
     * @param multiplicativeSplits Cache for multiplicative SPLITs.
     * @return The relevant nodes reachable from the specified node.
     */
    public static CpxNodeSets getCpxNodeSetsForPathsFromNode(
        final PrologEvaluationGraph graph,
        final CpxNodeSets sets,
        final Node<PrologAbstractState> node,
        final Set<Node<PrologAbstractState>> multiplicativeSplits)
    {
        final Set<Node<PrologAbstractState>> visited = new LinkedHashSet<Node<PrologAbstractState>>();
        final Set<Node<PrologAbstractState>> instanceSet = new LinkedHashSet<Node<PrologAbstractState>>();
        final Set<Node<PrologAbstractState>> splitSet = new LinkedHashSet<Node<PrologAbstractState>>();
        final Set<Node<PrologAbstractState>> parallelSet = new LinkedHashSet<Node<PrologAbstractState>>();
        final Set<Node<PrologAbstractState>> successSet = new LinkedHashSet<Node<PrologAbstractState>>();
        final Set<Node<PrologAbstractState>> instanceChildren = new LinkedHashSet<Node<PrologAbstractState>>();
        final Queue<Node<PrologAbstractState>> todo = new ArrayDeque<Node<PrologAbstractState>>();
        todo.offer(node);
        while (!todo.isEmpty()) {
            Node<PrologAbstractState> current = todo.poll();
            if (visited.contains(current)) {
                continue;
            }
            visited.add(current);
            if (sets.getInstanceNodes().contains(current)) {
                instanceSet.add(current);
                current = graph.getFirstChild(current);
                instanceChildren.add(current);
                todo.offer(current);
            } else if (sets.getSplitNodes().contains(current)) {
                splitSet.add(current);
                if (!multiplicativeSplits.contains(current)) {
                    todo.offer(graph.getFirstChild(current));
                    todo.offer(graph.getLastChild(current));
                }
            } else if (sets.getParallelNodes().contains(current)) {
                parallelSet.add(current);
                todo.offer(graph.getFirstChild(current));
                todo.offer(graph.getLastChild(current));
            } else if (sets.getSuccessNodes().contains(current)) {
                successSet.add(current);
                todo.offer(graph.getFirstChild(current));
            } else {
                for (final Node<PrologAbstractState> child : graph.getOut(current)) {
                    todo.offer(child);
                }
            }
        }
        return new CpxNodeSets(instanceSet, successSet, parallelSet, splitSet, instanceChildren);
    }

    /**
     * Computes a map from successors of multiplicative SPLIT nodes and the
     * root node to those multiplicative SPLIT nodes which they can reach
     * without traversing other multiplicative SPLIT nodes.
     * @param graph The graph to consider.
     * @param multiplicativeSplits Cache for multiplicative SPLITs.
     * @param aborter For abortions...
     * @return A map to reachable multiplicative SPLITs.
     * @throws AbortionException If it is aborted...
     */
    private static Map<Node<PrologAbstractState>, Set<Node<PrologAbstractState>>> calculateReachableMultiplicativeSplits(
        final PrologEvaluationGraph graph,
        final Set<Node<PrologAbstractState>> multiplicativeSplits,
        final Abortion aborter) throws AbortionException
    {
        final Map<Node<PrologAbstractState>, Set<Node<PrologAbstractState>>> res =
            new LinkedHashMap<Node<PrologAbstractState>, Set<Node<PrologAbstractState>>>();
        final Set<Node<PrologAbstractState>> starts = new LinkedHashSet<Node<PrologAbstractState>>();
        starts.add(graph.getRoot());
        for (final Node<PrologAbstractState> split : multiplicativeSplits) {
            starts.add(graph.getFirstChild(split));
            starts.add(graph.getLastChild(split));
        }
        final Set<Node<PrologAbstractState>> visited = new LinkedHashSet<Node<PrologAbstractState>>();
        final Set<Node<PrologAbstractState>> reachable = new LinkedHashSet<Node<PrologAbstractState>>();
        final Queue<Node<PrologAbstractState>> todo = new ArrayDeque<Node<PrologAbstractState>>();
        for (final Node<PrologAbstractState> start : starts) {
            visited.clear();
            reachable.clear();
            todo.clear();
            todo.offer(start);
            while (!todo.isEmpty()) {
                aborter.checkAbortion();
                final Node<PrologAbstractState> current = todo.poll();
                if (visited.contains(current)) {
                    continue;
                }
                visited.add(current);
                if (multiplicativeSplits.contains(current)) {
                    reachable.add(current);
                } else {
                    for (final Node<PrologAbstractState> child : graph.getOut(current)) {
                        todo.offer(child);
                    }
                }
            }
            res.put(start, new LinkedHashSet<Node<PrologAbstractState>>(reachable));
        }
        return res;
    }

    /**
     * Realizes the combination of subproblems according to multiplicative
     * SPLITs.
     * @param graph The graph to consider.
     * @param cdtProblems A map from starting nodes of subgraphs to CdtProblems
     *                    which have to be combined.
     * @param reachableMultis A map from the same starting nodes to those
     *                        multiplicative SPLIT nodes which can be reached
     *                        from them without traversing other multiplicative
     *                        SPLIT nodes.
     * @return A combined obligation according to multiplicative SPLITs.
     */
    private static BasicObligation combineToComplexProblem(
        PrologEvaluationGraph graph,
        Map<Node<PrologAbstractState>, CdtProblem> cdtProblems,
        Map<Node<PrologAbstractState>, Set<Node<PrologAbstractState>>> reachableMultis
    ) {
        final Node<PrologAbstractState> root = graph.getRoot();
        if (cdtProblems.size() == 1) {
            return cdtProblems.get(root);
        }
        // each problem contains all rules and cdts from all problems -
        // only the part to be counted is the set of cdts from a single problem
        //
        // reachability is only needed to combine obligations correctly
        final Set<Rule> allRules = new LinkedHashSet<Rule>();
        final Set<Cdt> allCdts = new LinkedHashSet<Cdt>();
        final Set<FunctionSymbol> allComp = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> allDefR = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> allDefP = new LinkedHashSet<FunctionSymbol>();
        for (final CdtProblem problem : cdtProblems.values()) {
            //TODO check that all rules and cdts are fresh
            allRules.addAll(problem.getR());
            allCdts.addAll(problem.getTuples());
            allComp.addAll(problem.getCompoundSymbols());
            allDefR.addAll(problem.getDefinedRSymbols());
            allDefP.addAll(problem.getDefinedPSymbols());
        }
        // TODO STRANGE: the last two arguments of the following call should be swapped
        // - however, that seems to be the way it works...
        final CdtProblem proto = CdtProblem.uncheckedCreate(allRules, allCdts, allComp, allDefP, allDefR);
        //        throw new UnsupportedOperationException("Not yet implemented");
        return
            PrologToCdtProblemTransformer.createComplexMaxObligation(
                root,
                graph,
                proto,
                cdtProblems,
                reachableMultis
            );
    }

    /**
     * Realizes the additive part of the combination of subproblems.
     * @param node The node to consider for combination.
     * @param graph The graph containing the node.
     * @param proto The CdtProblem for the whole graph.
     * @param cdtProblems A map from starting nodes of subgraphs to CdtProblems
     *                    which have to be combined.
     * @param reachableMultis A map from the same starting nodes to those
     *                        multiplicative SPLIT nodes which can be reached
     *                        from them without traversing other multiplicative
     *                        SPLIT nodes.
     * @return The additive combination of the reachable subproblems from the
     *         specified node.
     */
    private static ComplexCdtProblem createComplexMaxObligation(
        Node<PrologAbstractState> node,
        PrologEvaluationGraph graph,
        CdtProblem proto,
        Map<Node<PrologAbstractState>, CdtProblem> cdtProblems,
        Map<Node<PrologAbstractState>, Set<Node<PrologAbstractState>>> reachableMultis
    ) {
        Set<ComplexCdtProblem> complex = new LinkedHashSet<ComplexCdtProblem>();
        for (Node<PrologAbstractState> split : reachableMultis.get(node)) {
            complex.add(PrologToCdtProblemTransformer.createComplexMultObligation(
                split,
                graph,
                proto,
                cdtProblems,
                reachableMultis));
        }
        return
            new ComplexCdtProblem(
                Collections.singleton(proto.setS(cdtProblems.get(node).getTuples())),
                complex,
                false
            );
    }

    /**
     * Realizes the multiplicative part of the combination of subproblems.
     * @param split The SPLIT node to consider for combination.
     * @param graph The graph containing the node.
     * @param proto The CdtProblem for the whole graph.
     * @param cdtProblems A map from starting nodes of subgraphs to CdtProblems
     *                    which have to be combined.
     * @param reachableMultis A map from the same starting nodes to those
     *                        multiplicative SPLIT nodes which can be reached
     *                        from them without traversing other multiplicative
     *                        SPLIT nodes.
     * @return The multiplicative combination of the reachable subproblems from
     *         the specified node.
     */
    private static ComplexCdtProblem createComplexMultObligation(
        final Node<PrologAbstractState> split,
        final PrologEvaluationGraph graph,
        final CdtProblem proto,
        final Map<Node<PrologAbstractState>, CdtProblem> cdtProblems,
        final Map<Node<PrologAbstractState>, Set<Node<PrologAbstractState>>> reachableMultis)
    {
        final Node<PrologAbstractState> left = graph.getFirstChild(split);
        final Node<PrologAbstractState> right = graph.getLastChild(split);
        if (reachableMultis.get(left).isEmpty()) {
            if (reachableMultis.get(right).isEmpty()) {
                final Set<CdtProblem> concrete = new LinkedHashSet<CdtProblem>(2);
                concrete.add(proto.setS(cdtProblems.get(left).getTuples()));
                concrete.add(proto.setS(cdtProblems.get(right).getTuples()));
                return new ComplexCdtProblem(concrete, Collections.<ComplexCdtProblem>emptySet(), true);
            } else {
                return new ComplexCdtProblem(
                    Collections.singleton(proto.setS(cdtProblems.get(left).getTuples())),
                    Collections.singleton(PrologToCdtProblemTransformer.createComplexMaxObligation(
                        right,
                        graph,
                        proto,
                        cdtProblems,
                        reachableMultis)), true);
            }
        } else {
            if (reachableMultis.get(right).isEmpty()) {
                return new ComplexCdtProblem(
                    Collections.singleton(proto.setS(cdtProblems.get(right).getTuples())),
                    Collections.singleton(PrologToCdtProblemTransformer.createComplexMaxObligation(
                        left,
                        graph,
                        proto,
                        cdtProblems,
                        reachableMultis)), true);
            } else {
                final Set<ComplexCdtProblem> complex = new LinkedHashSet<ComplexCdtProblem>(2);
                complex.add(PrologToCdtProblemTransformer.createComplexMaxObligation(
                    left,
                    graph,
                    proto,
                    cdtProblems,
                    reachableMultis));
                complex.add(PrologToCdtProblemTransformer.createComplexMaxObligation(
                    right,
                    graph,
                    proto,
                    cdtProblems,
                    reachableMultis));
                return new ComplexCdtProblem(Collections.<CdtProblem>emptySet(), complex, true);
            }
        }
    }

    /**
     * Checks whether the derivation graph is decomposable.
     * @param graph The graph to consider.
     * @param multiplicativeSplits Cache for multiplicative SPLITs.
     * @return True if the specified graph is decomposable.
     */
    private static boolean isDecomposable(PrologEvaluationGraph graph, Set<Node<PrologAbstractState>> multiplicativeSplits) {
        LinkedHashSet<Cycle<PrologAbstractState>> sccs = graph.getSCCs();
        for (Node<PrologAbstractState> split : multiplicativeSplits) {
            for (Cycle<PrologAbstractState> scc : sccs) {
                if (scc.contains(split)) {
                    for (Node<PrologAbstractState> child : graph.getOut(split)) {
                        if (scc.contains(child)) {
                            return false;
                        }
                    }
                    break;
                }
            }
        }
        return true;
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getQuery().getPurpose().equals(PrologPurpose.COMPLEXITY);
    }

    @Override
    protected Logger getLogger() {
        return PrologToCdtProblemTransformer.log;
    }

    @Override
    protected Result processGraph(final PrologEvaluationGraph graph, final Abortion aborter) throws AbortionException {
        long time = 0;
        if (PrologToCdtProblemTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime();
        }
        //        Set<CpxTrsProblem> pps = new LinkedHashSet<CpxTrsProblem>();
        final Map<Integer, String> nodeLabels = new LinkedHashMap<Integer, String>();
        final BasicObligation obligation =
            PrologToCdtProblemTransformer.calculateCdtProblemsFromGraph(graph, nodeLabels, aborter);
        aborter.checkAbortion();
        //        pps.add(problemFromGraph);
        if (PrologToCdtProblemTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime() - time;
            PrologToCdtProblemTransformer.log.log(Level.FINE, "Reading CdtProblems: {0}ms\n", time / 1000000);
        }
        if (obligation == null) {
            return ResultFactory.unsuccessful("Constructed graph is no complexity graph!");
        }
        return ResultFactory.proved(obligation, UpperBound.create(), new PrologToCdtProblemTransformerProof(
            graph,
            this.options.isExportTree(),
            this.options.getTreeLimit(),
            nodeLabels));
    }

}
