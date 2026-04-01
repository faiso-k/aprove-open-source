package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This abstract class represents state positions defined for some stack frame.
 * @author cotto
 */
public abstract class StackFramePosition extends RootPosition {

    /**
     * The position of the stack frame in the call stack.
     */
    private final int frameNum;

    /**
     * Create a new abstract position representing some reference in the stack
     * frame at the given position in the callstack.
     * @param frame the position of the frame in the callstack
     */
    protected StackFramePosition(final int frame) {
        this.frameNum = frame;
    }

    /**
     * @return the position of the stack frame in the call stack.
     */
    public int getFrameNumber() {
        return this.frameNum;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final AbstractVariableReference getFromState(final State state,
        final boolean failOK,
        final Map<StatePosition, AbstractVariableReference> cache) {
        final StackFrame sf = this.getFrame(state);
        if (failOK && sf == null) {
            return null;
        }
        return this.getFromState(state, sf);
    }

    /**
     * @param state a state
     * @return the stack frame referenced from this position
     */
    protected StackFrame getFrame(final State state) {
        return state.getCallStack().get(this.frameNum);
    }

    /**
     * @param state a state
     * @param frame the stack frame containing the reference
     * @return the reference at the defined position contained in the given
     * stack frame
     */
    protected abstract AbstractVariableReference getFromState(final State state, final StackFrame frame);
}
