package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 *
 * @author cotto
 */
public class TerminationGraphToSingleGraph {
    /**
     * @param terminationGraph a Termination Graph consisting out of (possibly) many single method graphs, connected
     * with (implicit) edges
     * @param nodeToMethodGraphMap a map that gives the method graph for each (new) node
     * @param oldToNewMap a mapping for nodes
     * @return a single graph containing only explicit edges
     */
    public static JBCGraph createSingleGraph(
        final TerminationGraph terminationGraph,
        final Map<Node, MethodGraph> nodeToMethodGraphMap,
        final Map<Node, Node> oldToNewMap)
    {
        /*
         * Merge method graphs into one graph, make call/return edges
         * explicit. We then search for the SCCs and encode these as
         * separate problems to IDP. For each node, note in which method
         * graph it is.
         */
        final JBCGraph termGraph = new JBCGraph();
        final Collection<MethodGraph> graphs = terminationGraph.getMethodGraphs();
        for (final MethodGraph methodGraph : graphs) {
            for (final Node n : methodGraph.getNodes()) {
                final Node newN;

                if (!oldToNewMap.containsKey(n)) {
                    newN = new Node(n);
                    if (termGraph.addNode(newN)) {
                        oldToNewMap.put(n, newN);
                        nodeToMethodGraphMap.put(newN, methodGraph);
                    }
                }
            }
            for (final Edge e : methodGraph.getEdges()) {
                final EdgeInformation label = e.getLabel();
                final Node start = e.getStart();
                final Node end = e.getEnd();

                assert (methodGraph.containsNode(start));
                assert (methodGraph.containsNode(end));

                if (label instanceof MethodSkipEdge) {
                    final MethodSkipEdge mse = (MethodSkipEdge) label;
                    if (!graphs.contains(mse.getGraph())) {
                        continue;
                    }
                    if (!mse.getGraph().containsNode(mse.getNode())) {
                        continue;
                    }
                }
                termGraph.addEdge(oldToNewMap.get(start), label, oldToNewMap.get(end));
            }
        }

        for (final MethodGraph methodGraph : terminationGraph.getMethodGraphs()) {
            //Find all implicit incoming edges and add them:
            for (final MethodEndListener listener : methodGraph.getMethodEndListeners()) {
                if (!terminationGraph.getMethodGraphs().contains(listener.getMethodGraph())) {
                    continue;
                }
                boolean found = false;
                Node startNode = null;
                for (final Edge edge : listener.getNode().getOutEdges()) {
                    if (edge.getLabel() instanceof CallAbstractEdge) {
                        found = true;
                        /*
                         * There may be a chain of instance edges following the
                         * call abstraction.
                         */
                        Node tempNode = edge.getEnd();
                        Set<Edge> outEdges = tempNode.getOutEdges();
                        while (!outEdges.isEmpty()) {
                            tempNode = outEdges.iterator().next().getEnd();
                            outEdges = tempNode.getOutEdges();
                        }
                        startNode = oldToNewMap.get(tempNode);
                        break;
                    }
                }
                assert (found) : "Could not find source of call";
                final Node endNode;
                if (oldToNewMap.containsKey(methodGraph.getStartNode())) {
                    endNode = oldToNewMap.get(methodGraph.getStartNode());
                } else {
                    endNode = new Node(methodGraph.getStartNode());
                    oldToNewMap.put(methodGraph.getStartNode(), endNode);
                    nodeToMethodGraphMap.put(endNode, methodGraph);
                }
                termGraph.addEdge(startNode, new InstanceEdgeBetweenGraphs(), endNode);
            }
        }

        return termGraph;
    }

    /**
     * @param terminationGraph a Termination Graph consisting out of (possibly) many single method graphs, connected
     * with (implicit) edges
     * @return a single graph containing only explicit edges
     */
    public static JBCGraph createSingleGraph(final TerminationGraph terminationGraph) {
        final Map<Node, Node> oldToNewMap = new LinkedHashMap<>();
        final Map<Node, MethodGraph> nodeToMethodGraphMap = new LinkedHashMap<>();
        return TerminationGraphToSingleGraph.createSingleGraph(terminationGraph, nodeToMethodGraphMap, oldToNewMap);
    }
}
