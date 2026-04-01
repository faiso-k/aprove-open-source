package aprove.input.Programs.prolog.processors;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.graph.rules.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * The PrologToComplexityProblemTransformer gathers static methods for complexity analysis of Prolog programs.
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */
public abstract class PrologToComplexityProblemTransformer {

    /**
     * Computes all connection paths and partitions them according to the
     * decomposition of the graph.
     * @param graph The graph to consider.
     * @param sets Cache for relevant nodes - already partitioned according to
     *             the graph's decomposition.
     * @param multiplicativeSplits Cashe for the multiplicative SPLIT nodes in
     *                             the graph.
     * @param aborter For abortions...
     * @return A partition of all connection paths together with a
     *         corresponding start node for the subgraph they belong to.
     * @throws AbortionException If it is aborted...
     */
    public static List<Pair<Node<PrologAbstractState>, Set<List<Node<PrologAbstractState>>>>> calculateAllConnectionPaths(
        final PrologEvaluationGraph graph,
        final List<Pair<Node<PrologAbstractState>, CpxNodeSets>> sets,
        final Set<Node<PrologAbstractState>> multiplicativeSplits,
        final Abortion aborter) throws AbortionException
    {
        final List<Pair<Node<PrologAbstractState>, Set<List<Node<PrologAbstractState>>>>> res =
            new ArrayList<Pair<Node<PrologAbstractState>, Set<List<Node<PrologAbstractState>>>>>();
        for (final Pair<Node<PrologAbstractState>, CpxNodeSets> setPair : sets) {
            final CpxNodeSets set = setPair.y;
            final Set<List<Node<PrologAbstractState>>> resSet = new LinkedHashSet<List<Node<PrologAbstractState>>>();
            if (setPair.x.equals(graph.getRoot())) {
                resSet.addAll(PrologToComplexityProblemTransformer.calculateAllConnectionPathsFromNode(
                    graph,
                    setPair.x,
                    new ArrayList<Node<PrologAbstractState>>(),
                    set,
                    aborter));
            }
            for (final Node<PrologAbstractState> node : set.getInstanceChildren()) {
                aborter.checkAbortion();
                resSet.addAll(PrologToComplexityProblemTransformer.calculateAllConnectionPathsFromNode(
                    graph,
                    node,
                    new ArrayList<Node<PrologAbstractState>>(),
                    set,
                    aborter));
            }
            for (final Node<PrologAbstractState> node : set.getSplitNodes()) {
                aborter.checkAbortion();
                if (multiplicativeSplits.contains(node)) {
                    continue;
                }
                PrologToComplexityProblemTransformer.addPathsFromBothChildren(node, graph, set, resSet, aborter);
            }
            for (final Node<PrologAbstractState> node : set.getParallelNodes()) {
                aborter.checkAbortion();
                PrologToComplexityProblemTransformer.addPathsFromBothChildren(node, graph, set, resSet, aborter);
            }
            res.add(new Pair<Node<PrologAbstractState>, Set<List<Node<PrologAbstractState>>>>(setPair.x, resSet));
        }
        return res;
    }

    /**
     * Computes the set of multiplicative SPLITs in the specified graph.
     * @param graph The graph to consider.
     * @param sets Cashe for relevant nodes in the graph.
     * @param aborter For abortions...
     * @return The set of multiplicative SPLITs in the specified graph.
     * @throws AbortionException If it is aborted...
     */
    public static Set<Node<PrologAbstractState>> calculateMultiplicativeSplits(
        final PrologEvaluationGraph graph,
        final CpxNodeSets sets,
        final Abortion aborter) throws AbortionException
    {
        final Set<Node<PrologAbstractState>> res = new LinkedHashSet<Node<PrologAbstractState>>();
        for (final Node<PrologAbstractState> split : sets.getSplitNodes()) {
            if (aborter.isAborted()) {
                return null;
            }
            final Node<PrologAbstractState> child = graph.getFirstChild(split);
            //TODO use CSC, but be careful with self-reaching SPLITs!
            if (!graph.isDeterministic(child, aborter)) {
                res.add(split);
            }
        }
        return res;
    }

    /**
     * Returns true if the specified graph contains a PARALLEL node which can backtrack a substitution. This check is
     * only necessary if one considers non-ground variables, since substitutions on ground variables are never
     * backtracked!
     * @param graph The graph to examine.
     * @param cpxSet The relevant nodes for complexity analysis.
     * @param aborter For abortions...
     * @return True if the specified graph contains a PARALLEL node which can backtrack a substitution. False otherwise.
     */
    public static boolean hasEvilParallel(
        final PrologEvaluationGraph graph,
        final CpxNodeSets cpxSet,
        final Abortion aborter)
    {
        final Set<Node<PrologAbstractState>> visited = new LinkedHashSet<Node<PrologAbstractState>>();
        final Queue<Node<PrologAbstractState>> queue = new ArrayDeque<Node<PrologAbstractState>>();
        queue.addAll(cpxSet.getParallelNodes());
        while (!queue.isEmpty()) {
            final Node<PrologAbstractState> node = queue.poll();
            if (!visited.contains(node)) {
                visited.add(node);
                if (node.getObject().getState().size() > 1) {
                    for (final Edge<AbstractInferenceRule, PrologAbstractState> edge : graph.getInEdges(node)) {
                        final AbstractInferenceRule rule = edge.getObject();
                        switch (rule.rule()) {
                        case EVAL:
                            final EvalRule evalrule = (EvalRule) rule;
                            if (evalrule.getClash() == null && !evalrule.getSubstitution().isEmpty()) {
                                return true;
                            }
                            break;
                        case UNIFY_CASE:
                            final UnifyCaseRule unifyrule = (UnifyCaseRule) rule;
                            if (unifyrule.getClash() == null && !unifyrule.getSubstitution().isEmpty()) {
                                return true;
                            }
                            break;
                        case ONLY_EVAL:
                            if (!((OnlyEvalRule) rule).getSubstitution().isEmpty()) {
                                return true;
                            }
                            break;
                        case UNIFY_SUCCESS:
                            if (!((UnifySuccessRule) rule).getSubstitution().isEmpty()) {
                                return true;
                            }
                            break;
                        default:
                            // do nothing
                        }
                        queue.offer(edge.getStartNode());
                    }
                }
            }
        }
        return false;
    }

    /**
     * Checks whether the complexity for a concrete state represented by the specified node can be asymptotically
     * increased after reaching a success, i.e., our usual rule construction for split nodes without a second call to
     * the first successor would not be correct.
     * @param node The node.
     * @param graph The graph containing the node.
     * @param aborter For abortions...
     * @return True if the complexity can be increased after reaching a success from this node.
     * @throws AbortionException If it is aborted...
     */
    public static boolean hasPotentialComplexityIncreaseAfterSuccess(
        final Node<PrologAbstractState> node,
        final PrologEvaluationGraph graph,
        final Abortion aborter) throws AbortionException
    {
        return PrologToComplexityProblemTransformer.hasPotentialComplexityIncreaseAfterSuccess(
            node,
            graph,
            new LinkedHashSet<Node<PrologAbstractState>>(),
            aborter);
    }

    /**
     * Adds all paths from successors of PARALLEL or SPLIT nodes to resSet. This method just joins common code.
     * @param node The PARALLEL or SPLIT node.
     * @param graph The graph containing the node.
     * @param set The set of relevant nodes for paths.
     * @param resSet The set where to add the paths to.
     * @param aborter For abortions...
     * @throws AbortionException If it is aborted...
     */
    private static void addPathsFromBothChildren(
        final Node<PrologAbstractState> node,
        final PrologEvaluationGraph graph,
        final CpxNodeSets set,
        final Set<List<Node<PrologAbstractState>>> resSet,
        final Abortion aborter) throws AbortionException
    {
        resSet.addAll(PrologToComplexityProblemTransformer.calculateAllConnectionPathsFromNode(
            graph,
            graph.getFirstChild(node),
            new ArrayList<Node<PrologAbstractState>>(),
            set,
            aborter));
        resSet.addAll(PrologToComplexityProblemTransformer.calculateAllConnectionPathsFromNode(
            graph,
            graph.getLastChild(node),
            new ArrayList<Node<PrologAbstractState>>(),
            set,
            aborter));
    }

    /**
     * Computes all connection paths starting from the specified node together
     * with the specified prefix.
     * @param graph The graph containing the node.
     * @param node The start node to consider.
     * @param currentPath The prefix of the connection path.
     * @param sets Cache for relevant nodes.
     * @param aborter For abortions...
     * @return All connection paths starting from the specified node.
     * @throws AbortionException If it is aborted...
     */
    private static Set<List<Node<PrologAbstractState>>> calculateAllConnectionPathsFromNode(
        final PrologEvaluationGraph graph,
        final Node<PrologAbstractState> node,
        final List<Node<PrologAbstractState>> currentPath,
        final CpxNodeSets sets,
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
        if (nextPath.size() > 1 && PrologToComplexityProblemTransformer.isNonSuccessEndNode(node, sets)) {
            res.add(nextPath);
        } else if (!sets.getInstanceNodes().contains(node)
            && !sets.getSplitNodes().contains(node)
            && !sets.getParallelNodes().contains(node)
            && !(nextPath.size() > 1 && sets.getInstanceChildren().contains(node)))
        {
            for (final Node<PrologAbstractState> child : graph.getOut(node)) {
                aborter.checkAbortion();
                res.addAll(PrologToComplexityProblemTransformer.calculateAllConnectionPathsFromNode(
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
     * Checks whether the specified node can reach a cycle.
     * @param node The node.
     * @param graph The graph containing the node.
     * @param aborter For abortions...
     * @return True if the node can reach a cycle in the graph.
     * @throws AbortionException If it is aborted...
     */
    private static boolean canReachCycle(
        final Node<PrologAbstractState> node,
        final PrologEvaluationGraph graph,
        final Abortion aborter) throws AbortionException
    {
        return PrologToComplexityProblemTransformer.canReachCycle(
            node,
            graph,
            new LinkedHashSet<Node<PrologAbstractState>>(),
            aborter);
    }

    /**
     * Checks whether the specified node can reach a cycle.
     * @param node The node.
     * @param graph The graph containing the node.
     * @param visited Already visited states.
     * @param aborter For abortions...
     * @return True if the node can reach a cycle in the graph.
     * @throws AbortionException If it is aborted...
     */
    private static boolean canReachCycle(
        final Node<PrologAbstractState> node,
        final PrologEvaluationGraph graph,
        final Set<Node<PrologAbstractState>> visited,
        final Abortion aborter) throws AbortionException
    {
        aborter.checkAbortion();
        if (visited.contains(node)) {
            return true;
        }
        final Set<Node<PrologAbstractState>> next = new LinkedHashSet<Node<PrologAbstractState>>(visited);
        next.add(node);
        for (final Node<PrologAbstractState> child : graph.getOut(node)) {
            if (PrologToComplexityProblemTransformer.canReachCycle(child, graph, next, aborter)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether the complexity for a concrete state represented by the specified node can be asymptotically
     * increased after reaching a success, i.e., our usual rule construction for split nodes without a second call to
     * the first successor would not be correct. It returns false if it examines an already visited state.
     * @param node The node.
     * @param graph The graph containing the node.
     * @param visited The visited states.
     * @param aborter For abortions...
     * @return True if the complexity can be increased after reaching a success from this node.
     * @throws AbortionException If it is aborted...
     */
    private static boolean hasPotentialComplexityIncreaseAfterSuccess(
        final Node<PrologAbstractState> node,
        final PrologEvaluationGraph graph,
        final Set<Node<PrologAbstractState>> visited,
        final Abortion aborter) throws AbortionException
    {
        aborter.checkAbortion();
        if (visited.contains(node)) {
            return false;
        }
        if (graph.isSuccessNode(node)) {
            return PrologToComplexityProblemTransformer.canReachCycle(node, graph, aborter);
        }
        final Set<Node<PrologAbstractState>> next = new LinkedHashSet<Node<PrologAbstractState>>(visited);
        next.add(node);
        for (final Node<PrologAbstractState> child : graph.getOut(node)) {
            if (PrologToComplexityProblemTransformer.hasPotentialComplexityIncreaseAfterSuccess(
                child,
                graph,
                next,
                aborter))
            {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether the specified node is an end node, but no success node.
     * @param node The node to check.
     * @param sets The relevant nodes in the graph for the check.
     * @return True is the specified node is an end node, but no success node.
     */
    private static boolean isNonSuccessEndNode(final Node<PrologAbstractState> node, final CpxNodeSets sets) {
        return sets.getInstanceChildren().contains(node)
            || sets.getInstanceNodes().contains(node)
            || sets.getSplitNodes().contains(node)
            || sets.getParallelNodes().contains(node);
    }

}
