package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Do not delete! The class RootInputReference cannot also be a position (for
 * itself) because equals() for root input reference state positions should only
 * compare the original position, not the current reference name (and boolean
 * flag).
 * @author cotto
 */
public final class RootIRPosition extends InputRefRootPosition {
    /**
     * For each root position we only use a single position object.
     */
    private static final Map<Pair<StackFramePosition, Integer>, RootIRPosition> MAP = new LinkedHashMap<>();

    /**
     * The original position referenced by the root IR.
     */
    private final StackFramePosition origPos;

    /**
     * The number of the stack frame containing this reference (most of the
     * times this is 0).
     */
    private final int frameNum;

    /**
     * Create a new position for a root IR.
     * @param pos the position referenced by the root IR.
     * @param frame the number of the stack frame containing this reference
     * (most of the times this is 0).
     */
    private RootIRPosition(final StackFramePosition pos, final int frame) {
        this.origPos = pos;
        this.frameNum = frame;

    }

    /**
     * @return a position for a root IR.
     * @param pos the position referenced by the root IR.
     * @param frameNum the number of the stack frame containing this reference
     * (most of the times this is 0).
     */
    public static RootIRPosition create(final StackFramePosition pos, final int frameNum) {
        final Pair<StackFramePosition, Integer> pair = new Pair<StackFramePosition, Integer>(pos, frameNum);
        RootIRPosition result = RootIRPosition.MAP.get(pair);
        if (result == null) {
            synchronized (RootIRPosition.class) {
                result = RootIRPosition.MAP.get(pair);
                if (result == null) {
                    result = new RootIRPosition(pos, frameNum);
                    RootIRPosition.MAP.put(pair, result);
                }
            }
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference getFromState(
        final State state,
        final boolean failOK,
        final Map<StatePosition, AbstractVariableReference> cache)
    {
        final StackFrame frame = state.getCallStack().get(this.frameNum);
        if (failOK && frame == null) {
            return null;
        }
        final RootInputReference rir = frame.getInputReferences().getRootInputReference(this.origPos);
        if (failOK && rir == null) {
            return null;
        }
        return rir.getReference();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        sb.append("RIR(");
        this.origPos.toString(sb);
        sb.append(", ");
        sb.append(this.frameNum);
        sb.append(")");
    }
}
