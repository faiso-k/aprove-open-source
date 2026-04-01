package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class represents state positions for some element of the opstack in the
 * given stackframe.
 * @author cotto
 */
public final class OpStackRootPosition extends StackFramePosition {
    /**
     * For each frame and position we only use a single position object.
     */
    private static final Map<Pair<Integer, Integer>, OpStackRootPosition> MAP =
        new LinkedHashMap<Pair<Integer, Integer>, OpStackRootPosition>();

    /**
     * The position inside the opstack.
     */
    private final int pos;

    /**
     * Create a new position for the reference contained in the given frame's
     * opstack at the given position.
     * @param frame the position of the stackframe in the callstack.
     * @param position the position of the reference in the frame's opstack.
     */
    private OpStackRootPosition(final int frame, final int position) {
        super(frame);
        this.pos = position;
    }

    /**
     * @return a position for the reference contained in the given frame's
     * opstack at the given position.
     * @param frame the position of the stackframe in the callstack.
     * @param position the position of the reference in the frame's opstack.
     */
    public static OpStackRootPosition create(final int frame, final int position) {
        final Pair<Integer, Integer> pair =
            new Pair<Integer, Integer>(frame, position);
        OpStackRootPosition result = OpStackRootPosition.MAP.get(pair);
        if (result == null) {
            synchronized (OpStackRootPosition.class) {
                result = OpStackRootPosition.MAP.get(pair);
                if (result == null) {
                    result = new OpStackRootPosition(frame, position);
                    OpStackRootPosition.MAP.put(pair, result);
                }
            }
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference getFromState(final State state,
        final StackFrame frame) {
        return frame.getOperandStack().peek(this.pos);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        sb.append("os_");
        sb.append(super.getFrameNumber());
        sb.append('_');
        sb.append(this.pos);
    }
}
