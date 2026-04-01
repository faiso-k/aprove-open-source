package aprove.verification.oldframework.Utility.Graph;

import java.util.*;

/**
 * This class represents an edge of a graph, the attached object can freely be
 * changed, it _does_ account for equality
 * @param <E> type of the edge labels
 * @param <N> type of the nodes
 * @author Carsten Otto
 */
public class EdgeEquality<E, N> extends Edge<Collection<E>, N> {
    /**
     * A unique ID.
     */
    private static final long serialVersionUID = 1705522184496046874L;

    /**
     * Create a new edge without label.
     * @param startNode the start node
     * @param endNode the end node
     */
    public EdgeEquality(final Node<N> startNode, final Node<N> endNode) {
        super(startNode, endNode);
    }

    /**
     * Generates an edge and assigns objects to it.
     * @param startNode The node at the edge's start.
     * @param endNode The node at the edge's end.
     * @param objects The objects that belongs to this edge.
     */
    public EdgeEquality(final Node<N> startNode, final Node<N> endNode,
            final Collection<E> objects) {
        super(startNode, endNode, objects);
    }

    /**
     * Generates an edge and assigns objects to it.
     * @param startNode The node at the edge's start.
     * @param endNode The node at the edge's end.
     * @param objects The objects that belongs to this edge.
     */
    public EdgeEquality(final Node<N> startNode, final Node<N> endNode,
            final E object) {
        super(startNode, endNode, Collections.singleton(object));
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime * result
                + ((super.endNode == null) ? 0 : super.endNode.hashCode());
        result =
            prime * result
                + ((super.object == null) ? 0 : super.object.hashCode());
        result =
            prime * result
                + ((super.startNode == null) ? 0 : super.startNode.hashCode());
        return result;
    }

    @SuppressWarnings("unchecked")
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
        final Edge other = (Edge) obj;
        if (super.endNode == null) {
            if (other.endNode != null) {
                return false;
            }
        } else if (!super.endNode.equals(other.endNode)) {
            return false;
        }
        if (super.object == null) {
            if (other.object != null) {
                return false;
            }
        } else if (!super.object.equals(other.object)) {
            return false;
        }
        if (super.startNode == null) {
            if (other.startNode != null) {
                return false;
            }
        } else if (!super.startNode.equals(other.startNode)) {
            return false;
        }
        return true;
    }
}
