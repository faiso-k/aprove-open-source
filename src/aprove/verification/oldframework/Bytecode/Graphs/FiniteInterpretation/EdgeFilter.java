package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

/**
 * Interface used to allow filtering edges in graph searches such as path or SCC computation.
 * @author Marc Brockschmidt
 */
public interface EdgeFilter {
    /**
     * @param from the start node of the edge
     * @param to the end node of the edge
     * @param e the edge
     * @return true only for edges that are accepted by the filter
     */
    boolean selectEdge(final Node from, final Node to, final EdgeInformation e);
}
