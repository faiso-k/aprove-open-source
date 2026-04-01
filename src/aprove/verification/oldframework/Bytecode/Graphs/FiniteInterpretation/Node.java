package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;
import java.util.concurrent.atomic.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * Representation of nodes in our JBCGraph.
 * All operations modifying the node (adding and removing actions) must be called from JBCGraph or its subclasses.
 *
 * @author Marc Brockschmidt
 */
public class Node {
    /** The next free id number.*/
    private static AtomicInteger nextNodeNumber = new AtomicInteger(1);

    /**
     * The enclosed state of this node.
     */
    private final State state;

    /**
     * The outgoing edges of this node.
     */
    private final Set<Edge> outgoingEdges = new LinkedHashSet<>();

    /**
     * The incoming edges of this node.
     */
    private final Set<Edge> incomingEdges = new LinkedHashSet<>();

    /**
     * The outgoing edges of this node to hidden nodes.
     */
    private final Set<Edge> hiddenOutgoingEdges = new LinkedHashSet<>();

    /**
     * The incoming edges of this node from hidden nodes.
     */
    private final Set<Edge> hiddenIncomingEdges = new LinkedHashSet<>();

    /**
     * An unique id number for this node.
     */
    private final int nodeNumber;

    /**
     * @param s some state.
     */
    public Node(final State s) {
        this.state = s;
        this.nodeNumber = Node.nextNodeNumber.getAndIncrement();
    }

    /**
     * Creates a new node object with the same state and ID, but different
     * edge sets.
     * @param oldNode some existing node.
     */
    public Node(final Node oldNode) {
        this.state = oldNode.getState();
        this.nodeNumber = oldNode.getNodeNumber();
    }

    /**
     * @param inEdge some incoming edge
     * @return true iff this edge was stored and removed.
     */
    boolean removeIncomingEdge(final Edge inEdge) {
        return this.incomingEdges.remove(inEdge);
    }

    boolean hideIncomingEdge(final Edge inEdge) {
        if (this.incomingEdges.remove(inEdge)) {
            this.hiddenIncomingEdges.add(inEdge);
            return true;
        }
        return false;
    }

    /**
     * @param outEdge some outgoing edge
     * @return true iff this edge was stored and removed.
     */
    boolean removeOutgoingEdge(final Edge outEdge) {
        return this.outgoingEdges.remove(outEdge);
    }

    boolean hideOutgoingEdge(final Edge outEdge) {
        if (this.outgoingEdges.remove(outEdge)) {
            this.hiddenOutgoingEdges.add(outEdge);
            return true;
        }
        return false;
    }

    /**
     * Adds an outgoing edge.
     *
     * @param e some edge
     * @return true iff the edge was not stored yet.
     */
    boolean addOutgoingEdge(final Edge e) {
        return this.outgoingEdges.add(e);
    }

    /**
     * Adds an incoming edge.
     *
     * @param e some edge
     * @return true iff the edge was not stored yet.
     */
    boolean addIncomingEdge(final Edge e) {
        return this.incomingEdges.add(e);
    }

    void remove() {
        for (Edge e : this.incomingEdges) {
            e.getStart().removeOutgoingEdge(e);
        }
        for (Edge e : this.outgoingEdges) {
            e.getEnd().removeIncomingEdge(e);
        }
    }

    void hide() {
        for (Edge e : this.incomingEdges) {
            e.getStart().hideOutgoingEdge(e);
        }
        for (Edge e : this.outgoingEdges) {
            e.getEnd().hideIncomingEdge(e);
        }
        this.hiddenIncomingEdges.addAll(this.incomingEdges);
        this.incomingEdges.clear();
        this.hiddenOutgoingEdges.addAll(this.outgoingEdges);
        this.outgoingEdges.clear();
    }

    /**
     * @return the enclosed state.
     */
    public State getState() {
        return this.state;
    }

    /**
     * @return the unique ID of this node
     */
    public int getNodeNumber() {
        return this.nodeNumber;
    }

    /**
     * @return the set of incoming edges (DO NOT MODIFY, THIS IS THE INTERNAL
     *  STRUCTURE)
     */
    public Set<Edge> getInEdges() {
        return this.incomingEdges;
    }

    /**
     * @return the set of hidden incoming edges (DO NOT MODIFY, THIS IS THE INTERNAL
     *  STRUCTURE)
     */
    public Set<Edge> getHiddenInEdges() {
        return this.hiddenIncomingEdges;
    }

    /**
     * @return the set of outgoing edges (DO NOT MODIFY, THIS IS THE INTERNAL
     *  STRUCTURE)
     */
    public Set<Edge> getOutEdges() {
        return this.outgoingEdges;
    }

    /**
     * @return the set of hidden outgoing edges (DO NOT MODIFY, THIS IS THE INTERNAL
     *  STRUCTURE)
     */
    public Set<Edge> getHiddenOutEdges() {
        return this.hiddenOutgoingEdges;
    }

    /**
     * @return true iff there is a predecessor.
     */
    public boolean hasPredecessor() {
        return !this.incomingEdges.isEmpty();
    }

    /**
     * @return true iff n has an incoming refinement or split edge
     */
    public boolean hasRefineOrSplitPredIn(Collection<Node> interestingNodes) {
        /*
         * We are not interested in nodes that have a SPLIT or REFINE
         * predecessor, as these predecessors are more general than the
         * SPLIT or REFINE successor.
         */
        for (final Edge inEdge : incomingEdges) {
            if (inEdge.getLabel() instanceof RefinementOrSplitEdge && interestingNodes.contains(inEdge.getStart())) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return true iff n has an outgoing call abstract edge
     */
    public boolean hasCallAbstractSuccIn(Collection<Node> interestingNodes) {
        for (final Edge outEdge : outgoingEdges) {
            if (outEdge.getLabel() instanceof CallAbstractEdge && interestingNodes.contains(outEdge.getEnd())) {
                return true;
            }
        }
        return false;
    }

    public boolean hasInstanceSucc() {
        return this.hasInstanceSuccIn(null);
    }

    /**
     * @return true iff n has an outgoing instance edge
     */
    public boolean hasInstanceSuccIn(Collection<Node> interestingNodes) {
        /*
         * We are not interested in nodes that have an INSTANCE
         * successor, as these successors are more general than the
         * INSTANCE predecessor.
         */
        for (final Edge outEdge : outgoingEdges) {
            if (outEdge.getLabel() instanceof InstanceEdge && (interestingNodes == null || interestingNodes.contains(outEdge.getEnd()))) {
                return true;
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return this.nodeNumber;
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

        final Node other = (Node) obj;
        if (this.nodeNumber != other.nodeNumber) {
            return false;
        }

        return true;
    }

    /**
     * @return a text representation of this node.
     */
    @Override
    public String toString() {
        return this.nodeNumber + "";// + ": " + this.state.toString();
    }
}
