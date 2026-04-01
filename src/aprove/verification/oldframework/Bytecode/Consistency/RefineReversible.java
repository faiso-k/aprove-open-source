/**
 *
 */
package aprove.verification.oldframework.Bytecode.Consistency;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * @author christian This class asserts, that for every refinement edge an
 * instance edge in the other direction can be drawn
 */
public class RefineReversible implements Checker {
    /**
     * The graph to check
     */
    private final MethodGraph graph;

    /**
     * Null if the check has succeeded or was not started. Otherwise this points
     * to an edge which could not be reversed by an instance edge.
     */
    private Edge malEdge;

    /**
     * @param g The graph to check
     */
    public RefineReversible(final MethodGraph g) {
        this.graph = g;
        this.malEdge = null;
    }

    /**
     * Walk through the graph and check that for every refinement edge we can
     * draw an instance edge in the other direction.
     * @return true iff no problem was found
     */
    @Override
    public boolean check() {
        this.graph.getGraphLock().readLock().lock();
        try {
            for (final Edge e : this.graph.getEdges()) {
                final Node startNode = e.getStart();
                final Node endNode = e.getEnd();
                final EdgeInformation label = e.getLabel();
                if (label instanceof RefinementEdge) {
                    final State startState = startNode.getState();
                    final State endState = endNode.getState();
                    final JBCMerger m = new PathMerger();

                    // try endState ---instance---> startState
                    AbstractVariableReference replacementRef = null;
                    AbstractVariableReference replacedRef = null;
                    if (label instanceof EQRefinementEdge) {
                        replacementRef =
                            ((EQRefinementEdge) label).getReplacementRef();
                        replacedRef =
                            ((EQRefinementEdge) label).getReplacedRef();
                    }
                    if (!m.isInstance(endState, startState, replacementRef,
                        replacedRef)) {
                        this.malEdge = e;
                        return false;
                    }
                }
            }
            return true;
        } finally {
            this.graph.getGraphLock().readLock().unlock();
        }
    }

    @Override
    public String toString() {
        if (this.malEdge == null) {
            return "Check passed.";
        }
        return this.malEdge + " cannot be reversed by an instance edge";
    }
}
