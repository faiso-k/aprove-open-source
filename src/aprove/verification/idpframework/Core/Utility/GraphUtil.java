package aprove.verification.idpframework.Core.Utility;

import java.util.*;

import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class GraphUtil {

    public static Set<INode> collectNodes(final Collection<IEdge> edges) {
        final LinkedHashSet<INode> res = new LinkedHashSet<INode>();

        for (final IEdge edge : edges) {
            res.add(edge.from);
            res.add(edge.to);
        }

        return res;
    }

    public static Set<IDPSubGraph> cleanupSubGraphs(final Collection<? extends IDPSubGraph> subGraphs) {
        final Set<IDPSubGraph> result = new LinkedHashSet<IDPSubGraph>();
        for (final IDPSubGraph subGraph : subGraphs) {
            boolean isLargest = true;

            final Iterator<IDPSubGraph> resultIterator = result.iterator();
            while (resultIterator.hasNext()) {
                final IDPSubGraph resGraph = resultIterator.next();
                if (subGraph.containsAll(resGraph)) {
                    resultIterator.remove();
                } else if (resGraph.containsAll(subGraph)) {
                    isLargest = false;
                    break;
                }
            }

            if (isLargest) {
                result.add(subGraph);
            }
        }

        return result;
    }

    public static Set<IDPSubGraph> cleanupRemovedEdges(final IDependencyGraph graph, final Collection<? extends IDPSubGraph> subGraphs) {
        final Set<IDPSubGraph> result = new LinkedHashSet<IDPSubGraph>();
        for (final IDPSubGraph subGraph : subGraphs) {
            final LinkedHashSet<IEdge> newEdges = new LinkedHashSet<IEdge>(subGraph.getEdges());
            if (newEdges.retainAll(graph.getEdges())) {
                result.add(new IDPSubGraph(ImmutableCreator.create(newEdges)));
            } else {
                result.add(subGraph);
            }
        }

        return result;
    }

}
