package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * The PrologToTRSTransformer builds a PrologDerivationGraph
 * and extracts a TRS from it whose termination
 * guarantees termination of the original PrologProgram.
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */

public class PrologToTRSTransformer extends PrologGraphProcessor {

    /**
     * @author cryingshadow
     * Proof for this processor.
     */
    public class PrologToTRSTransformerProof extends PrologGraphProcessorProof implements DOT_Able {

        /**
         * Standard constructor.
         * @param petGraph The graph.
         * @param exportGraph Flag indicating whether to export the graph graphically.
         * @param exportLimit Limit on the number of nodes up to which the graph is exported graphically (if at all).
         * @param nodeLabels To keep the connection between the graph and the proof.
         */
        public PrologToTRSTransformerProof(
            final PrologEvaluationGraph petGraph,
            final boolean exportGraph,
            final int exportLimit,
            final Map<Integer, String> nodeLabels)
        {
            super(petGraph, exportGraph, exportLimit, nodeLabels);
        }

        @Override
        protected String getProofMessage() {
            // TODO: add citation
            return "Transformed Prolog program to TRS.";
        }

    }

    /**
     * Logger.
     */
    private static final Logger log =
        Logger.getLogger("aprove.input.Programs.prolog.processors.PrologToTRSTransformer");

    /**
     * Standard constructor.
     * @param args The arguments of this processor.
     */
    @ParamsViaArgumentObject
    public PrologToTRSTransformer(final PrologOptions args) {
        super(args);
    }

    /**
     * The main method of this processor. It calculates a TRS from the specified graph whose
     * termination implies termination of the original PrologProgram.
     * @param graph The graph to consider.
     * @param nodeLabels Mapping from node numbers to labels.
     * @param aborter For abortions...
     * @return The obligation returned by this processor.
     * @throws AbortionException If it is aborted...
     */
    public static Set<Rule> calculateTRSFromGraph(
        final PrologEvaluationGraph graph,
        final Map<Integer, String> nodeLabels,
        final Abortion aborter) throws AbortionException
    {
        final Set<Rule> res = new LinkedHashSet<Rule>();
        final TermNodeSets sets = graph.getTermNodeSetsForPaths(aborter);
        final Set<String> used = new LinkedHashSet<String>();
        used.add("U");
        used.add("X");
        used.add("f");
        final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_FUNCS);
        final GroundnessAnalysis ground = AbstractGraphBuilderHeuristic.generateGroundnessAnalysis(graph);
        for (final List<Node<PrologAbstractState>> path : PrologToTRSTransformer.calculateAllTerminationPaths(
            graph,
            sets,
            aborter))
        {
            res.addAll(RuleConstructor.buildConnectionRules(path, graph, ground, fridge, aborter));
        }
        for (final Node<PrologAbstractState> split : sets.getSplitNodes()) {
            res.addAll(RuleConstructor.buildSplitRules(split, graph, ground, false, fridge, aborter));
        }
        return res;
    }

    /**
     * Calculates all termination paths in the given graph. A termination path starts in the root or a successor of an
     * instance, generalization, or split node. It ends in an instance, generalization, split, or success node or the
     * successor of an instance or generalization node. It may not traverse instance, generalization, or split nodes or
     * successors of instance or generalization nodes in between.
     * @param graph The graph to consider.
     * @param sets The relevant nodes.
     * @param aborter For abortions...
     * @return The set of all termination paths in the graph.
     * @throws AbortionException If it is aborted...
     */
    private static Set<List<Node<PrologAbstractState>>> calculateAllTerminationPaths(
        final PrologEvaluationGraph graph,
        final TermNodeSets sets,
        final Abortion aborter) throws AbortionException
    {
        final Set<List<Node<PrologAbstractState>>> res = new LinkedHashSet<List<Node<PrologAbstractState>>>();
        res.addAll(PrologToTRSTransformer.calculateAllTerminationPathsFromNode(
            graph,
            graph.getRoot(),
            new ArrayList<Node<PrologAbstractState>>(),
            sets,
            aborter));
        for (final Node<PrologAbstractState> node : sets.getInstanceChildren()) {
            aborter.checkAbortion();
            res.addAll(PrologToTRSTransformer.calculateAllTerminationPathsFromNode(
                graph,
                node,
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                aborter));
        }
        for (final Node<PrologAbstractState> node : sets.getSplitNodes()) {
            aborter.checkAbortion();
            res.addAll(PrologToTRSTransformer.calculateAllTerminationPathsFromNode(
                graph,
                graph.getFirstChild(node),
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                aborter));
            res.addAll(PrologToTRSTransformer.calculateAllTerminationPathsFromNode(
                graph,
                graph.getLastChild(node),
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                aborter));
        }
        return res;
    }

    /**
     * Calculates all termination paths in the given graph starting from the specified node with the specified
     * currentPath as prefix.
     * @param graph The graph to consider.
     * @param node The start node.
     * @param currentPath The prefix.
     * @param sets The relevant nodes.
     * @param aborter For abortions...
     * @return A set of all termination paths in the given graph starting from the specified node with the specified
     *         currentPath as prefix.
     * @throws AbortionException If it is aborted...
     */
    private static Set<List<Node<PrologAbstractState>>> calculateAllTerminationPathsFromNode(
        final PrologEvaluationGraph graph,
        final Node<PrologAbstractState> node,
        final List<Node<PrologAbstractState>> currentPath,
        final TermNodeSets sets,
        final Abortion aborter) throws AbortionException
    {
        aborter.checkAbortion();
        List<Node<PrologAbstractState>> nextPath = new ArrayList<Node<PrologAbstractState>>(currentPath);
        nextPath.add(node);
        final Set<List<Node<PrologAbstractState>>> res = new LinkedHashSet<List<Node<PrologAbstractState>>>();
        if (nextPath.size() > 1 && sets.getSuccessNodes().contains(node)) {
            res.add(nextPath);
            nextPath = new ArrayList<Node<PrologAbstractState>>(nextPath);
        }
        if (nextPath.size() > 1 && PrologToTRSTransformer.isNonSuccessEndNode(node, sets)) {
            res.add(nextPath);
        } else if (!sets.getInstanceNodes().contains(node)
            && !sets.getSplitNodes().contains(node)
            && !(nextPath.size() > 1 && sets.getInstanceChildren().contains(node)))
        {
            for (final Node<PrologAbstractState> child : graph.getOut(node)) {
                aborter.checkAbortion();
                res.addAll(PrologToTRSTransformer.calculateAllTerminationPathsFromNode(
                    graph,
                    child,
                    nextPath,
                    sets,
                    aborter));
                nextPath = new ArrayList<Node<PrologAbstractState>>(nextPath);
            }
        }
        return res;
    }

    /**
     * Checks whether the specified node is an end node, but no success node.
     * @param node The node to check.
     * @param sets The relevant nodes in the graph for the check.
     * @return True is the specified node is an end node, but no success node.
     */
    private static boolean isNonSuccessEndNode(final Node<PrologAbstractState> node, final TermNodeSets sets) {
        return sets.getInstanceChildren().contains(node)
            || sets.getInstanceNodes().contains(node)
            || sets.getSplitNodes().contains(node);
    }

    @Override
    protected Logger getLogger() {
        return PrologToTRSTransformer.log;
    }

    @Override
    protected Result processGraph(final PrologEvaluationGraph graph, final Abortion aborter) throws AbortionException {
        long time = 0;
        if (PrologToTRSTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime();
        }
        final Map<Integer, String> nodeLabels = new LinkedHashMap<Integer, String>();
        final Set<Rule> trs = PrologToTRSTransformer.calculateTRSFromGraph(graph, nodeLabels, aborter);
        if (trs == null) {
            return ResultFactory.aborted("program extraction took too long");
        }
        if (PrologToTRSTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime() - time;
            PrologToTRSTransformer.log.log(Level.FINE, "Reading new QTRSProblem: {0}ms\n", time / 1000000);
            time = System.nanoTime();
        }
        return ResultFactory
            .proved(
                QTRSProblem.create(ImmutableCreator.create(trs)),
                YNMImplication.SOUND,
                new PrologToTRSTransformerProof(
                    graph,
                    this.options.isExportTree(),
                    this.options.getTreeLimit(),
                    nodeLabels));
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getQuery().getPurpose().equals(PrologPurpose.TERMINATION);
    }

}
