package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import immutables.*;

/**
 * <p>
 * A position in a state, e.g. "Foo.x" for a static field "x" in a class "Foo"
 * or "frame0-LV2.next" for the value of the attribute "next" in the object
 * instance referenced from the third local variable in the first stackframe.
 * </p>
 * Note: For rather weird performance reasons, the compareTo method for the
 * Comparable interface does not behave fully as expected. See compareTo().
 * @author cotto
 */
public abstract class StatePosition implements Comparable<StatePosition>, Immutable {
    /**
     * @param n the array index
     * @return the position which is the extension of this position to the nth
     * array element (starting at 0)
     */
    public ArrayElementPosition appendArrayElement(final int n) {
        return ArrayElementPosition.create(this, n);
    }

    /**
     * @return the position which is the extension of this position to the
     * length of the array at this position.
     */
    public ArrayLengthPosition appendArrayLength() {
        return ArrayLengthPosition.create(this);
    }

    /**
     * @param id the field identifier
     * @return the position which is the extension of this position to the field
     * in the reference at this position.
     */
    public InstanceFieldPosition appendField(final FieldIdentifier id) {
        return InstanceFieldPosition.create(this, id);
    }

    /**
     * @param prefix a prefix of this position
     * @return all heap edges on the path from prefix to this
     */
    public Collection<HeapEdge> getEdgesTo(final StatePosition prefix) {
        return this.getSuffixOf(prefix).getHeapEdges();
    }

    /**
     * @param prefix a prefix of this position
     * @return all positions from this to the prefix, inclusive
     */
    public Collection<StatePosition> getPositionsDownTo(final StatePosition prefix) {
        final Collection<StatePosition> result = new LinkedHashSet<>();
        StatePosition currentPosition = this;
        while (currentPosition != null && currentPosition != prefix) {
            result.add(currentPosition);
            final NonRootPosition nonRoot = (NonRootPosition) currentPosition;
            currentPosition = nonRoot.getPrev();
        }
        result.add(prefix);
        return result;
    }

    /**
     * @param state a state
     * @return the reference at this position in the given state (state|_this)
     */
    public AbstractVariableReference getFromState(final State state) {
        return this.getFromState(state, false, null);
    }

    /**
     * @param state a state
     * @param failOK iff false, we assert that this is a valid position for the
     * state
     * @param cache a cache that may be used (may be null)
     * @return the reference at this position in the given state (state|_this)
     * (or null if it does not exist and failOK is set)
     */
    public abstract AbstractVariableReference getFromState(
        final State state,
        boolean failOK,
        Map<StatePosition, AbstractVariableReference> cache);

    /**
     * @param state a state
     * @param result a collection into which every reference on the path to this
     *  position is stored.
     * @return the last reference on this path (i.e. the one corresponding
     *  to the position <code>this</code>)
     */
    public abstract AbstractVariableReference getReferencesOnPath(
        State state,
        Collection<AbstractVariableReference> result);

    /**
     * @param that some state position
     * @return the longest StatePosition that is a prefix of this and that.
     */
    public StatePosition getMaxCommonPrefix(final StatePosition that) {
        StatePosition result = null;
        final Iterator<StatePosition> itThis = this.getPathToRoot().descendingIterator();
        final Iterator<StatePosition> itThat = that.getPathToRoot().descendingIterator();
        while (itThis.hasNext() && itThat.hasNext()) {
            final StatePosition thisCurrent = itThis.next();
            final StatePosition thatCurrent = itThat.next();
            if (thisCurrent != thatCurrent) {
                return result;
            }
            result = thisCurrent;
        }
        return result;
    }

    /**
     * Create a list of all positions from this position to the root.
     * @param toRoot a list of positions
     */
    public abstract void getPathToRoot(List<StatePosition> toRoot);

    /**
     * @return a list of all positions from the root to this position.
     */
    public List<StatePosition> getPathFromRoot() {
        final LinkedList<StatePosition> fromRoot = new LinkedList<>();
        this.getPathToRoot(fromRoot);
        final LinkedList<StatePosition> result = new LinkedList<>();
        final Iterator<StatePosition> pos = fromRoot.descendingIterator();
        while (pos.hasNext()) {
            result.add(pos.next());
        }
        return result;
    }

    /**
     * @return a list of all positions to the root from this position.
     */
    public LinkedList<StatePosition> getPathToRoot() {
        final LinkedList<StatePosition> toRoot = new LinkedList<>();
        this.getPathToRoot(toRoot);
        return toRoot;
    }

    /**
     * @return the root position of this state position.
     */
    public abstract RootPosition getRootPosition();

    /**
     * @param that some other state position
     * @return true iff this is a (non-proper?) prefix of the other position
     */
    public abstract boolean isPrefixOf(final StatePosition that);

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb);
        return sb.toString();
    }

    /**
     * Return a nice string representation using the given string builder.
     * @param sb a string builder.
     */
    public abstract void toString(StringBuilder sb);

    /**
     * If this is a prefix of the given state position, return a non-root state
     * position (starting in null) representing the suffix. For
     * xyzabc.getSuffixOf(xyz) the state position abc is returned.
     * @param prefix some state position which must be a prefix of this position
     * @return the suffix that appended to the prefix gives this position
     */
    public abstract NonRootPosition getSuffixOf(final StatePosition prefix);

    /**
     * @param newSuffix some fake non-root position starting in null
     * @return a new stateposition which results from prepending this position
     * to the argument position
     */
    public StatePosition append(final NonRootPosition newSuffix) {
        if (newSuffix == null) {
            return this;
        }
        return newSuffix.prepend(this);
    }

    /**
     * @return the number of single elements in this position
     */
    public abstract int length();

    /**
     * @return the heap edges from this position to the root
     */
    public Set<HeapEdge> getHeapEdges() {
        final Set<HeapEdge> result = new LinkedHashSet<>();
        for (final StatePosition pos : this.getPathToRoot()) {
            if (pos instanceof NonRootPosition) {
                if (!(pos instanceof InstanceFieldPosition)
                    || !((InstanceFieldPosition) pos).getFieldId().getFieldName().endsWith("!cycleJoint"))
                {
                    result.add(((NonRootPosition) pos).getHeapEdge());
                }
            }
        }
        return result;
    }

    /**
     * @param pos some position
     * @return the heap edges in the position (or the empty set if pos == null)
     */
    public static Set<HeapEdge> getHeapEdges(final StatePosition pos) {
        if (pos == null) {
            return Collections.<HeapEdge>emptySet();
        }
        return pos.getHeapEdges();
    }

    /**
     * <p>
     * Important: This does not what it normally should do!
     * </p>
     * Because we are only interested in finding a defined shortest position for
     * a given reference (see HeapPositions), we only need to distinguish the
     * shortest positions from each other and can return arbitrary results for
     * the other references.
     * @param other the StatePosition to compare with
     * @return see above
     */
    @Override
    public int compareTo(final StatePosition other) {
        if (this instanceof RootPosition) {
            if (other instanceof RootPosition) {
                final int x = System.identityHashCode(this);
                final int y = System.identityHashCode(other);
                return Integer.valueOf(x).compareTo(y);
            }
            return -1;
        }
        if (other instanceof RootPosition) {
            return 1;
        }
        return 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        // StatePositions are singletons
        return super.hashCode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        // StatePositions are singletons
        return super.equals(obj);
    }
}
