package aprove.verification.oldframework.Bytecode.Graphs;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * Only regard non-method return edges.
 */
public class EdgeTypeFilter implements EdgeFilter {
    /**
     * Class of edges to filter.
     */
    private final Class<? extends EdgeInformation> typeToFilter;

    /**
     * @param t Class of edges to filter.
     */
    public EdgeTypeFilter(final Class<? extends EdgeInformation> t) {
        this.typeToFilter = t;
    }

    /**
     * @param from the start node of the edge
     * @param to the end node of the edge
     * @param e the edge
     * @return true only for edges that go to a non-hidden node
     */
    @Override
    public boolean selectEdge(final Node from,
        final Node to,
        final EdgeInformation e) {
        return !(this.typeToFilter.isInstance(e));
    }
}
