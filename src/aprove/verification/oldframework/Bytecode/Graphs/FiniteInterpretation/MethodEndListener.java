package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Processors.ToGraph.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * A MethodEndListener receives updates to a {@link MethodEndNotifier} and
 * remembers the calling node. The notifier will dispatch the calls to the
 * approriate methods in the graph.
 * @author Fabian K&uuml;rten
 * @see MethodGraph#newMethodEnd(MethodGraph, State, Node)
 * @see MethodGraph#deletedMethodEnd(MethodGraph, State, Node)
 */
public class MethodEndListener {
    /**
     * The invoking node, i.e, a node which expects to get notified of
     * successors.
     */
    private final Node callingNode;

    /**
     * The method graph containing the node.
     */
    private final MethodGraph methodGraph;

    /**
     * Creates a new {@link MethodEndListener} for the given node (and of
     * course, in the context of this graph).
     * @param nodeParam a node which waits for new successors
     * @param methodGraphParam the graph containing the node
     */
    MethodEndListener(final Node nodeParam, final MethodGraph methodGraphParam) {
        this.methodGraph = methodGraphParam;
        this.callingNode = nodeParam;
    }

    /**
     * Called when an observed graph creates a new method end, that is a node
     * where the only stackframe is about to be popped. Common examples are
     * <code>return</code> instructions and uncaught exceptions.
     * <p>
     * The listening graph should reflect this change by adding a new successor
     * to any node that called the compatible method.
     * </p>
     * @param endingGraph some method graph
     * @param endingState some method end in g
     * @return a new state, which needs to be added to the graph and queue (null
     * if nothing needs to be done)
     */
    public Collection<MethodGraphWorker> newMethodEnd(final MethodGraph endingGraph, final State endingState) {
        return this.methodGraph.newMethodEnd(endingGraph, endingState, this.callingNode);
    }

    /**
     * @return the node that called some method
     */
    public Node getNode() {
        return this.callingNode;
    }

    /**
     * @return the method graph
     */
    public MethodGraph getMethodGraph() {
        return this.methodGraph;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.callingNode.toString() + " in graph " + this.methodGraph;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.callingNode == null) ? 0 : this.callingNode.hashCode());
        result = prime * result + ((this.methodGraph == null) ? 0 : this.methodGraph.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final MethodEndListener other = (MethodEndListener) obj;
        if (this.callingNode == null) {
            if (other.callingNode != null) {
                return false;
            }
        } else if (!this.callingNode.equals(other.callingNode)) {
            return false;
        }
        if (this.methodGraph == null) {
            if (other.methodGraph != null) {
                return false;
            }
        } else if (!this.methodGraph.equals(other.methodGraph)) {
            return false;
        }
        return true;
    }
}
