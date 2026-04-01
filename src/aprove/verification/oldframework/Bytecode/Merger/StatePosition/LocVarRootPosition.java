package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class represents state positions for the local variables in the
 * stackframes.
 * @author cotto
 */
public final class LocVarRootPosition extends StackFramePosition {
    /**
     * For each frame and position we only use a single position object.
     */
    private static final Map<Pair<Integer, Integer>, LocVarRootPosition> MAP =
        new LinkedHashMap<Pair<Integer, Integer>, LocVarRootPosition>();

    /**
     * The index of the local variable in the local variable array.
     */
    private final int varIndex;

    /**
     * Create a new state position representing the reference stored in the
     * local variable array at position 'index' of the given frame.
     * @param frame the position of the stackframe in the callstack.
     * @param index the index of the local variable in the local variable array.
     */
    private LocVarRootPosition(final int frame, final int index) {
        super(frame);
        this.varIndex = index;
    }

    /**
     * @return a state position representing the reference stored in the local
     * variable array at position 'index' of the given frame.
     * @param frame the position of the stackframe in the callstack.
     * @param index the index of the local variable in the local variable array.
     */
    public static LocVarRootPosition create(final int frame, final int index) {
        final Pair<Integer, Integer> pair =
            new Pair<Integer, Integer>(frame, index);
        LocVarRootPosition result = LocVarRootPosition.MAP.get(pair);
        if (result == null) {
            synchronized (LocVarRootPosition.class) {
                result = LocVarRootPosition.MAP.get(pair);
                if (result == null) {
                    result = new LocVarRootPosition(frame, index);
                    LocVarRootPosition.MAP.put(pair, result);
                }
            }
        }
        return result;
    }

    public int getVarIndex() {
        return varIndex;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference getFromState(final State state,
        final StackFrame frame) {
        return frame.getLocalVariable(this.varIndex);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        sb.append("lv_");
        sb.append(super.getFrameNumber());
        sb.append('_');
        sb.append(this.varIndex);
    }

    /**
     * Store the reference at this position in the state.
     * @param state a state
     * @param reference a reference
     */
    public void setInState(final State state,
        final AbstractVariableReference reference) {
        final StackFrame frame = this.getFrame(state);
        frame.setLocalVariable(this.varIndex, reference);
    }
}
