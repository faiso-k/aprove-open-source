package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * A root position, representing e.g. a local variable in some stack frame.
 * @author cotto
 */
public abstract class RootPosition extends StatePosition {
    /**
     * {@inheritDoc}
     */
    @Override
    public final NonRootPosition getSuffixOf(final StatePosition prefix) {
        assert (this == prefix);
        return null;
    }

    /**
     * {@inheritDoc}
     * @return
     */
    @Override
    public final int length() {
        return 1;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isPrefixOf(final StatePosition that) {
        return this == that.getRootPosition();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final RootPosition getRootPosition() {
        return this;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference getReferencesOnPath(
        final State state,
        final Collection<AbstractVariableReference> result)
    {
        final AbstractVariableReference nextRef = this.getFromState(state);
        result.add(nextRef);
        return nextRef;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final void getPathToRoot(final List<StatePosition> toRoot) {
        toRoot.add(this);
    }
}
