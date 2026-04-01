package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * This class represents state positions for the length attribute of an array.
 * @author cotto
 */
public final class ArrayLengthPosition extends NonRootPosition {
    /**
     * For each predecessor position only have a single object.
     */
    private static final Map<StatePosition, ArrayLengthPosition> MAP =
        new LinkedHashMap<StatePosition, ArrayLengthPosition>();

    /**
     * Create a new position referencing the length of an array.
     * @param prev the position of the array
     */
    private ArrayLengthPosition(final StatePosition prev) {
        super(prev);
    }

    /**
     * @return a position referencing the length of an array.
     * @param prev the position of the array
     */
    public static ArrayLengthPosition create(final StatePosition prev) {
        ArrayLengthPosition result = ArrayLengthPosition.MAP.get(prev);
        if (result == null) {
            synchronized (ArrayLengthPosition.class) {
                result = ArrayLengthPosition.MAP.get(prev);
                if (result == null) {
                    result = new ArrayLengthPosition(prev);
                    ArrayLengthPosition.MAP.put(prev, result);
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
        if (!(prevVar instanceof Array)) {
            throw PositionDoesNotExistException.INSTANCE;
        }
        final Array arr = (Array) prevVar;
        return arr.getLength();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected AbstractVariableReference getReferencesOnPath(final AbstractVariable prevVar,
            final AbstractVariableReference prevRef, final State state,
            final Collection<AbstractVariableReference> result) {
        assert (prevVar instanceof Array);
        final Array arr = (Array) prevVar;
        final AbstractVariableReference nextRef = arr.getLength();
        result.add(nextRef);
        return nextRef;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public HeapEdge getHeapEdge() {
        return new ArrayLengthEdge();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        super.toString(sb);
        sb.append(".length");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    NonRootPosition getCopyWithOtherPredecessor(final StatePosition newPred) {
        return ArrayLengthPosition.create(newPred);
    }
}
