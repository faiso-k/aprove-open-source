package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This class represents state positions for the exception parts of the
 * stackframes.
 * @author cotto
 */
public final class ExceptionRootPosition extends StackFramePosition {
    /**
     * For each frame we only use a single position object.
     */
    private static final Map<Integer, ExceptionRootPosition> MAP =
        new LinkedHashMap<Integer, ExceptionRootPosition>();

    /**
     * Create a new root position for the exception in some stack frame.
     * @param frame the position of the stack frame in the call stack.
     */
    private ExceptionRootPosition(final int frame) {
        super(frame);
    }

    /**
     * @return a root position for the exception in some stack frame.
     * @param frame the position of the stack frame in the call stack.
     */
    public static ExceptionRootPosition create(final int frame) {
        ExceptionRootPosition result = ExceptionRootPosition.MAP.get(frame);
        if (result == null) {
            synchronized (ExceptionRootPosition.class) {
                result = ExceptionRootPosition.MAP.get(frame);
                if (result == null) {
                    result = new ExceptionRootPosition(frame);
                    ExceptionRootPosition.MAP.put(frame, result);
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
        return frame.getException();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        sb.append("exc_");
        sb.append(super.getFrameNumber());
    }
}
