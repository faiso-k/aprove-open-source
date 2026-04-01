package aprove.verification.oldframework.Bytecode.Graphs;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * This filter takes care that a given set of nodes is not reached when calculating the reachable nodes.
 */
public class DontCrossNodesEdgeFilter implements EdgeFilter {
    private final Collection<Node> dontCross;
    private final MethodGraph graph;

    /**
     * Remember the nodes that should not be reached.
     * @param d some nodes
     * @param g the graph
     */
    public DontCrossNodesEdgeFilter(final Collection<Node> d, final MethodGraph g) {
        this.dontCross = d;
        this.graph = g;
    }

    /**
     * @param from the start node of the edge
     * @param to the end node of the edge
     * @param e the edge
     * @return false if the reached node is hidden or is contained in the set of nodes that may not be reached
     */
    @Override
    public boolean selectEdge(final Node from, final Node to, final EdgeInformation e) {
        return !this.dontCross.contains(to);
    }
}
