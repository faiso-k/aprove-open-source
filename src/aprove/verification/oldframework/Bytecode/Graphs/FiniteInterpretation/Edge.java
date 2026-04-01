package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of edges in our JBCGraphs.
 *
 * @author Marc Brockschmidt
 */
public class Edge {

    /**
     * mapping from references in the source state of the edge to a
     * collection of references that correspond to it in the target state.
     */
    private CollectionMap<AbstractVariableReference, AbstractVariableReference> refMappingStartToEnd;

    /**
     * mapping from references in the end state of the edge to a
     * collection of references that correspond to it in the start state.
     */
    private CollectionMap<AbstractVariableReference, AbstractVariableReference> refMappingEndToStart;

    /**
     * The start of this edge.
     */
    private final Node start;

    /**
     * The end of this edge.
     */
    private final Node end;

    /**
     * The label of this edge, containing hopefully useful information.
     */
    private final EdgeInformation label;

    /**
     * @param s start of this edge.
     * @param l label of this edge.
     * @param e end of this edge.
     */
    public Edge(final Node s, final EdgeInformation l, final Node e) {
        this.start = s;
        this.label = l;
        this.end = e;
    }

    /**
     * @return start of this edge.
     */
    public Node getStart() {
        return this.start;
    }

    /**
     * @return end of this edge.
     */
    public Node getEnd() {
        return this.end;
    }

    /**
     * @return label of this edge.
     */
    public EdgeInformation getLabel() {
        return this.label;
    }

    /**
     * @param heapPosCache a cache for heap positions (with primitives!)
     * @return mapping from references in the start state of the edge to a
     * collection of references that correspond to it in the end state.
     */
    public CollectionMap<AbstractVariableReference, AbstractVariableReference> getRefRenamingStartToEnd(
        final Map<State, HeapPositions> heapPosCache)
    {
        if (this.refMappingStartToEnd == null) {
            this.computeReferenceMappingOnEdge(heapPosCache);
        }

        return this.refMappingStartToEnd;
    }

    /**
     * @param heapPosCache a cache for heap positions (with primitives!)
     * @return mapping from references in the end state of the edge to a
     * collection of references that correspond to it in the start state.
     */
    public CollectionMap<AbstractVariableReference, AbstractVariableReference> getRefRenamingEndToStart(
        final Map<State, HeapPositions> heapPosCache)
    {
        if (this.refMappingEndToStart == null) {
            this.computeReferenceMappingOnEdge(heapPosCache);
        }

        return this.refMappingEndToStart;
    }

    /**
     * Computes a mapping between references in the source and target of
     * <code>edge</code>.
     * @param heapPosCache a cache for heap positions (with primitives!)
     */
    private void computeReferenceMappingOnEdge(final Map<State, HeapPositions> heapPosCache) {
        final CollectionMap<AbstractVariableReference, AbstractVariableReference> newMapStartToEnd =
            new CollectionMap<AbstractVariableReference, AbstractVariableReference>();
        final CollectionMap<AbstractVariableReference, AbstractVariableReference> newMapEndToStart =
            new CollectionMap<AbstractVariableReference, AbstractVariableReference>();

        final State startState = this.start.getState();
        final State endState = this.end.getState();

        final HeapPositions startHeapPos = Edge.getHeapPos(startState, heapPosCache);
        final HeapPositions endHeapPos = Edge.getHeapPos(endState, heapPosCache);

        for (final AbstractVariableReference startR : startState.getReferences().keySet()) {
            if (startR.isNULLRef()) {
                continue;
            }
            final Collection<StatePosition> startRPositions = startHeapPos.getPositionsForRef(startR);
            final Set<AbstractVariableReference> endRefs = new LinkedHashSet<>();
            for (final StatePosition startRPos : startRPositions) {
                final AbstractVariableReference endRCand = endHeapPos.getReferenceForPos(startRPos, true);
                //Position does not exist in this state
                if (endRCand == null) {
                    continue;
                }
                endRefs.add(endRCand);
            }
            if (endRefs.size() > 1) {
                //We allow non-1:1-mappings in this direction for instance edges:
                if (this.label instanceof InstanceEdge) {
                    newMapStartToEnd.add(startR, endRefs);
                }
            } else if (endRefs.size() == 1) {
                newMapStartToEnd.add(startR, endRefs);
            }
        }

        for (final AbstractVariableReference endR : endState.getReferences().keySet()) {
            if (endR.isNULLRef()) {
                continue;
            }
            final Collection<StatePosition> endRPositions = endHeapPos.getPositionsForRef(endR);
            final Set<AbstractVariableReference> startRefs = new LinkedHashSet<>();
            for (final StatePosition endRPos : endRPositions) {
                final AbstractVariableReference startRCand = startHeapPos.getReferenceForPos(endRPos, true);
                //Position does not exist in this state
                if (startRCand == null) {
                    continue;
                }
                startRefs.add(startRCand);
            }
            if (startRefs.size() > 1) {
                //We allow non-1:1-mappings in this direction for instance edges:
                if (this.label instanceof RefinementEdge) {
                    newMapEndToStart.add(endR, startRefs);
                }
            } else if (startRefs.size() == 1) {
                newMapEndToStart.add(endR, startRefs);
            }
        }

        this.refMappingStartToEnd = newMapStartToEnd;
        this.refMappingEndToStart = newMapEndToStart;
    }

    /**
     * @return the heap positions object for the given state, which also
     * includes primitives. If a cache is provided, it is used properly.
     * @param state a state
     * @param heapPosCache a cache for known HeapPositions objects
     */
    private static HeapPositions getHeapPos(final State state, final Map<State, HeapPositions> heapPosCache) {
        HeapPositions result;
        if (heapPosCache != null) {
            result = heapPosCache.get(state);
            if (result == null) {
                result = new HeapPositions(state, true);
                heapPosCache.put(state, result);
            }
            return result;
        }
        return new HeapPositions(state, true);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.start + " --[ " + this.label.getClass().getSimpleName() + ": " + this.label + "]--> " + this.end;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.end == null) ? 0 : this.end.hashCode());
        result = prime * result + ((this.label == null) ? 0 : this.label.hashCode());
        result = prime * result + ((this.start == null) ? 0 : this.start.hashCode());
        return result;
    }

    /** {@inheritDoc} */
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
        if (this.end == null) {
            if (other.end != null) {
                return false;
            }
        } else if (!this.end.equals(other.end)) {
            return false;
        }
        if (this.label == null) {
            if (other.label != null) {
                return false;
            }
        } else if (!this.label.equals(other.label)) {
            return false;
        }
        if (this.start == null) {
            if (other.start != null) {
                return false;
            }
        } else if (!this.start.equals(other.start)) {
            return false;
        }
        return true;
    }
}
