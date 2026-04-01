package aprove.verification.oldframework.Utility.Profiling.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * properties for QDependencyGraph
 * @author Tim Enger
 */

public class QDGraphProperties {
    public enum Properties {
        /** the smallest number of edges whose removal disconnects the graph */
        EdgeConnectivity,
        /** number of edges */
        Size,
        /** number of vertices */
        Order,
        /** maximum number of outgoing edges of all vertices */
        MaxOutgoingEdges,
        /** average outgoing edges */
        AvgOutgoingEdges
    }

    public static EnumMap<Properties, Integer> computeProperties(QDependencyGraph qdg) {
        Map<Properties, Integer> map = new LinkedHashMap<Properties, Integer>();

        Graph<Rule, ?> graph = qdg.getGraph();

        int maxOutgoingEdges = QDGraphProperties.computeMaxOutgoingEdges(graph);
        int avgOutgoingEdges = 0;

        if(graph.getNodes().size() > 0){
            avgOutgoingEdges = maxOutgoingEdges / graph.getNodes().size();
        }

        map.put(Properties.EdgeConnectivity, QDGraphProperties.computeEdgeConnectivity(graph));
        map.put(Properties.Size, graph.getEdges().size());
        map.put(Properties.Order, graph.getNodes().size());
        map.put(Properties.MaxOutgoingEdges, maxOutgoingEdges);
        map.put(Properties.AvgOutgoingEdges, avgOutgoingEdges);

        return new EnumMap<Properties, Integer>(map);
    }

    private static <T> int computeEdgeConnectivity(Graph<Rule, T> graph) {
        Graph<Rule, T> modifiedGraph = graph.getCopy();
        Graph<Rule, T> tempGraph = modifiedGraph.getCopy();

        for (Edge<T, Rule> edge : graph.getEdges()) {
            tempGraph.removeEdge(edge);

            if (QDGraphProperties.isConnected(tempGraph)) {
                modifiedGraph = tempGraph;
            }
        }

        return modifiedGraph.getEdges().size();
    }

    private static boolean isConnected(Graph<Rule, ?> graph) {
        int maxNodes = graph.getNodes().size();
        int nodes = 0;

        if (maxNodes > 1) {
            Node<Rule> node = graph.getNodes().iterator().next();
            List<Node<Rule>> n = new ArrayList<Node<Rule>>();
            n.add(node);
            nodes = graph.determineReachableNodes(n).size();
        }

        return nodes == maxNodes;
    }

    private static int computeMaxOutgoingEdges(Graph<Rule, ?> graph) {
        int max = 0;
        int temp;

        for (Node<Rule> node : graph.getNodes()) {
            temp = graph.getOutEdges(node).size();
            max = Math.max(temp, max);
        }

        return max;
    }
}
