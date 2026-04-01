package aprove.verification.oldframework.Utility.Profiling.Utility;

import java.util.*;

import aprove.verification.dpframework.IDPProblem.idpGraph.*;

/**
 * properties for IDependencyGraph
 * @author Tim Enger
 */

public class IDGraphProperties {
    public enum Properties {
        /** the smallest number of edges whose removal disconnects the graph */
        // EdgeConnectivity,
        /** the greatest number of atoms of all Edges */
        // MaxAtoms,
        /** number of edges */
        Size,
        /** number of vertices */
        Order,
        /** maximum number of outgoing edges of all vertices */
        MaxOutgoingEdges,
        /** average outgoing edges */
        AvgOutgoingEdges
    }

    public static EnumMap<Properties, Integer> computeProperties(IIDependencyGraph idg) {
        Map<Properties, Integer> map = new LinkedHashMap<Properties, Integer>();

        int maxOutgoingEdges = IDGraphProperties.computeMaxOutgoingEdges(idg);
        int avgOutgoingEdges = 0;

        if (idg.getNodes().size() > 0) {
            avgOutgoingEdges = maxOutgoingEdges / idg.getNodes().size();
        }

        // map.put(Properties.EdgeConnectivity, computeEdgeConnectivity(idg));
        // map.put(Properties.EdgeConnectivity, computeMaxAtoms(idg));
        map.put(Properties.Size, idg.getEdges().size());
        map.put(Properties.Order, idg.getNodes().size());
        map.put(Properties.MaxOutgoingEdges, maxOutgoingEdges);
        map.put(Properties.AvgOutgoingEdges, avgOutgoingEdges);

        return new EnumMap<Properties, Integer>(map);
    }

    private static int computeMaxAtoms(IIDependencyGraph graph) {
        // TODO
        // visitor?
        return 0;
    }

    private static int computeEdgeConnectivity(IIDependencyGraph graph) {
        // TODO
        // need copy method
        return 0;
    }

    private static boolean isConnected(IIDependencyGraph graph) {
        // TODO
        // reachable nodes ?
        return false;
    }

    private static int computeMaxOutgoingEdges(IIDependencyGraph graph) {
        int max = 0;
        int temp;

        for (Node node : graph.getNodes()) {
            temp = graph.getOutDegree(node);
            max = Math.max(temp, max);
        }

        return max;
    }
}