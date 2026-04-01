package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;

/**
 * A root input reference is used to deal with input references that occur in
 * every call to a specific method, i.e. arguments. The connection needed when
 * returning from the called method is done using a state position.
 * @author cotto
 */
public class RootInputReference extends InputReference implements Cloneable {
    /**
     * The corresponding StatePosition in the invoking state.
     */
    private final StackFramePosition position;

    /**
     * @param ref the reference we are dealing with
     * @param pos the corresponding StatePosition in the invoking state
     */
    public RootInputReference(final AbstractVariableReference ref, final StackFramePosition pos) {
        super(ref);
        this.position = pos;
    }

    /**
     * @param b true iff the stored information visible from the reference was
     * changed.
     * @param ref the reference we are dealing with
     * @param pos the corresponding StatePosition in the invoking state
     */
    private RootInputReference(RootInputReference original) {
        super(original);
        this.position = original.position;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RootInputReference clone() {
        return new RootInputReference(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference getOriginalReference(final State callingState) {
        return callingState.getReference(this.position);
    }

    /**
     * @return the position
     */
    public StackFramePosition getPosition() {
        return this.position;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb, null, null, true);
        return sb.toString();
    }

    @Override
    public void toString(
        final StringBuilder sb,
        final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean shortRepresentation)
    {
        super.toString(sb, varUsers, state, shortRepresentation);
        sb.append('(');
        sb.append(this.position.toString());
        sb.append(')');
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RootIRPosition getIRStatePosition(final int frameNum) {
        return RootIRPosition.create(this.getPosition(), frameNum);
    }
}
