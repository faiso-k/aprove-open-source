package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This abstract class represents state positions which are no root positions.
 * Therefore, each represented position has a non-empty predecessor position.
 * @author cotto
 */
public abstract class NonRootPosition extends StatePosition {

    /**
     * The previous position.
     */
    private final StatePosition prev;

    /**
     * Create a new position referencing the given previous position.
     * @param prevPos the previous position
     */
    protected NonRootPosition(final StatePosition prevPos) {
        this.prev = prevPos;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isPrefixOf(final StatePosition that) {
        if (that instanceof RootPosition) {
            return false;
        }
        StatePosition currentThat = that;
        while (currentThat != null && currentThat != this) {
            if (currentThat instanceof NonRootPosition) {
                currentThat = ((NonRootPosition) currentThat).prev;
            } else {
                return false;
            }
        }
        return currentThat == this;
    }

    /**
     * @param prevVar the variable contained in the state at the position
     * defined by the previous position
     * @param prevRef the corresponding reference
     * @param state a state
     * @param result a collection into which every reference on the path to this
     *  position is stored.
     */
    protected abstract AbstractVariableReference getReferencesOnPath(
        AbstractVariable prevVar,
        AbstractVariableReference prevRef,
        State state,
        Collection<AbstractVariableReference> result);

    /**
     * @param prevVar the variable contained in the state at the position
     * defined by the previous position
     * @param prevRef the corresponding reference
     * @param state a state
     * @return the reference at this position in the given state (state|_this)
     * @throws PositionDoesNotExistException when the position does not exist
     */
    protected abstract AbstractVariableReference getFromState(
        AbstractVariable prevVar,
        AbstractVariableReference prevRef,
        State state) throws PositionDoesNotExistException;

    /**
     * {@inheritDoc}
     */
    @Override
    public final AbstractVariableReference getFromState(
        final State state,
        final boolean failOK,
        final Map<StatePosition, AbstractVariableReference> cache)
    {
        final AbstractVariableReference prevAVR;
        if (cache != null && cache.containsKey(this.prev)) {
            prevAVR = cache.get(this.prev);
        } else {
            prevAVR = this.prev.getFromState(state, failOK, cache);
        }
        if (failOK && prevAVR == null) {
            if (cache != null) {
                cache.put(this, null);
            }
            return null;
        }
        final AbstractVariable prevVar = state.getAbstractVariable(prevAVR);
        try {
            final AbstractVariableReference res = this.getFromState(prevVar, prevAVR, state);
            if (cache != null) {
                cache.put(this, res);
            }
            return res;
        } catch (final PositionDoesNotExistException e) {
            if (cache != null) {
                cache.put(this, null);
            }
            assert (failOK);
            return null;
        }
    }

    /**
     * @return for a NRP #.x.y.z return the reference at pos(ref).x.y.z (or null
     * if it does not exist)
     * @param ref the reference at the root of this NRP
     * @param state a state
     */
    public AbstractVariableReference getFromState(final AbstractVariableReference ref, final State state) {
        try {
            if (this.prev == null) {
                final AbstractVariable var = state.getAbstractVariable(ref);
                return this.getFromState(var, ref, state);
            }
            assert (this.prev instanceof NonRootPosition);
            final AbstractVariableReference prevRef = ((NonRootPosition) this.prev).getFromState(ref, state);
            if (prevRef == null) {
                return null;
            }
            final AbstractVariable prevVar = state.getAbstractVariable(prevRef);
            return this.getFromState(prevVar, prevRef, state);
        } catch (final PositionDoesNotExistException e) {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference getReferencesOnPath(
        final State state,
        final Collection<AbstractVariableReference> result)
    {
        final AbstractVariableReference prevAVR = this.prev.getReferencesOnPath(state, result);
        final AbstractVariable prevVar = state.getAbstractVariable(prevAVR);
        return this.getReferencesOnPath(prevVar, prevAVR, state, result);
    }

    /**
     * @return the corresponding heap edge to the last element of this position.
     */
    public abstract HeapEdge getHeapEdge();

    /**
     * {@inheritDoc}
     */
    @Override
    public final void getPathToRoot(final List<StatePosition> toRoot) {
        StatePosition current = this;
        while (current instanceof NonRootPosition) {
            toRoot.add(current);
            current = ((NonRootPosition) current).prev;
        }

        if (current != null) {
            toRoot.add(current);
        }
    }

    /**
     * @return the previous state position
     */
    public final StatePosition getPrev() {
        return this.prev;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final RootPosition getRootPosition() {
        return this.prev.getRootPosition();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final NonRootPosition getSuffixOf(final StatePosition prefix) {
        if (this == prefix) {
            return null;
        }
        return this.getCopyWithOtherPredecessor(this.prev.getSuffixOf(prefix));
    }

    /**
     * @param statePosition the new predecessor
     * @return a copy of this position where the predecessor is set to the state
     * position given in the argument
     */
    abstract NonRootPosition getCopyWithOtherPredecessor(StatePosition statePosition);

    /**
     * @return the first element of this position, which has a predecessor of
     * null.
     */
    public final NonRootPosition getFirstElement() {
        if (this.prev == null) {
            return this;
        }
        assert (this.prev instanceof NonRootPosition);
        return ((NonRootPosition) this.prev).getFirstElement();
    }

    /**
     * @param n define where to split
     * @return a pair of non-root positions where the second component is formed
     * out of the last n elements of this position (starting at null) and the
     * first component is the prefix.
     */
    public final Pair<NonRootPosition, NonRootPosition> split(final int n) {
        if (n == 0) {
            return new Pair<NonRootPosition, NonRootPosition>(this, null);
        }
        assert (this.prev instanceof NonRootPosition || this.prev == null);
        if (n == 1) {
            return new Pair<NonRootPosition, NonRootPosition>(
                (NonRootPosition) this.prev,
                this.getCopyWithOtherPredecessor(null));
        }
        final NonRootPosition p = (NonRootPosition) this.prev;
        final Pair<NonRootPosition, NonRootPosition> prevSplit = p.split(n - 1);
        return new Pair<NonRootPosition, NonRootPosition>(prevSplit.x, this.getCopyWithOtherPredecessor(prevSplit.y));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final int length() {
        if (this.prev == null) {
            return 1;
        }
        return 1 + this.prev.length();
    }

    /**
     * Prepend the given position to this non-root position, which must start at
     * null.
     * @param statePosition some state position
     * @return statePosition.this
     */
    public NonRootPosition prepend(final StatePosition statePosition) {
        if (this.prev == null) {
            return this.getCopyWithOtherPredecessor(statePosition);
        }
        assert (this.prev instanceof NonRootPosition);
        return this.getCopyWithOtherPredecessor(((NonRootPosition) this.prev).prepend(statePosition));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        if (this.prev == null) {
            sb.append("#");
        } else {
            this.getPrev().toString(sb);
        }
    }
}
