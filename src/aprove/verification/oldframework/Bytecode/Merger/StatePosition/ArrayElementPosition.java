package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class represents state positions for some element of an array. If pos'
 * is the position of some array a, then pos'n is the position of a[n].
 * @author cotto
 */
public final class ArrayElementPosition extends NonRootPosition {
    /**
     * For each predecessor position and index only have a single object.
     */
    private static final Map<Pair<StatePosition, Integer>, ArrayElementPosition> MAP = new LinkedHashMap<>();

    /**
     * The index of the referenced array element.
     */
    private final int index;

    /**
     * Create a new position referencing an array element.
     * @param prev the position of the array
     * @param n the index of the referenced element
     */
    private ArrayElementPosition(final StatePosition prev, final int n) {
        super(prev);
        this.index = n;
    }

    /**
     * @return a position referencing an array element.
     * @param prev the position of the array
     * @param n the index of the referenced element
     */
    public static ArrayElementPosition create(final StatePosition prev, final int n) {
        final Pair<StatePosition, Integer> pair = new Pair<>(prev, n);
        ArrayElementPosition result = ArrayElementPosition.MAP.get(pair);
        if (result == null) {
            synchronized (ArrayElementPosition.class) {
                result = ArrayElementPosition.MAP.get(pair);
                if (result == null) {
                    result = new ArrayElementPosition(prev, n);
                    ArrayElementPosition.MAP.put(pair, result);
                }
            }
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected AbstractVariableReference getFromState(final AbstractVariable prevVar,
        final AbstractVariableReference prevRef,
        final State state) throws PositionDoesNotExistException {
        if (!(prevVar instanceof ConcreteArray)) {
            throw PositionDoesNotExistException.INSTANCE;
        }
        return ((ConcreteArray) prevVar).get(state, prevRef, this.index);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected AbstractVariableReference getReferencesOnPath(final AbstractVariable prevVar,
        final AbstractVariableReference prevRef,
        final State state,
        final Collection<AbstractVariableReference> result) {
        assert (prevVar instanceof ConcreteArray);
        final AbstractVariableReference nextRef = ((ConcreteArray) prevVar).get(state, prevRef, this.index);
        result.add(nextRef);
        return nextRef;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public HeapEdge getHeapEdge() {
        return new ArrayMemberEdge(this.index);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        super.toString(sb);
        sb.append('[');
        sb.append(this.index);
        sb.append(']');
    }

    /**
     * {@inheritDoc}
     */
    @Override
    NonRootPosition getCopyWithOtherPredecessor(final StatePosition newPred) {
        return ArrayElementPosition.create(newPred, this.index);
    }
}
