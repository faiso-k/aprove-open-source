package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A non-root input reference is used for all input references that are specific
 * for a calling state, e.g. some reference sharing with an argument. The
 * connection needed when returning from the called method is done using the
 * calling state and the reference in that state.
 * @author cotto
 */
public class NonRootInputReference extends InputReference implements Cloneable, StateDeletionListener {
    /**
     * The references in the original states.
     */
    private final CollectionMap<State, AbstractVariableReference> originalReferences;

    /**
     * The state position for which this NRIR is created.
     */
    private final Pair<OpCode, StatePosition> position;

    /**
     * @param ref the reference we are dealing with
     * @param heapPosCallingState heap positions for the state that caused this
     * InputReference to exist.
     * @param origRef the reference in the calling state
     */
    public NonRootInputReference(
        final AbstractVariableReference ref,
        final AbstractVariableReference origRef,
        final HeapPositions heapPosCallingState)
    {
        super(ref);
        final StatePosition pos = heapPosCallingState.getShortestPositionForRef(ref);
        final State callingState = heapPosCallingState.getState();
        this.position = new Pair<>(callingState.getCallStack().get(1).getCurrentOpCode(), pos);
        assert (!(pos instanceof NonRootIRPosition));
        this.originalReferences = new CollectionMap<>();
        this.add(callingState, origRef);
    }

    /**
     * @param changed true iff the stored information visible from the reference
     * was changed.
     * @param ref the reference we are dealing with
     * @param callingState the state that caused this InputReference to exist.
     * @param origRef the reference in the calling state
     * @param posPair the pair of opcode and state position that denotes for
     * which position this NRIR should be used
     */
    private NonRootInputReference(
        final IRChangeInformations changeInformation,
        final AbstractVariableReference ref,
        final State callingState,
        final AbstractVariableReference origRef,
        final Pair<OpCode, StatePosition> posPair)
    {
        super(ref);
        this.setChanges(changeInformation);
        this.position = posPair;
        this.originalReferences = new CollectionMap<>();
        this.add(callingState, origRef);
    }

    /**
     * @param original the NonRootInputReference to copy from
     * @param cloneChangedBit if set, re-use the old changed bit. Otherwise set
     * it to false in the clone.
     */
    private NonRootInputReference(final NonRootInputReference original, final boolean cloneChangedBit) {
        super(original.getReference());
        if (cloneChangedBit) {
            this.setChanges(original.getChanges().copy());
        }
        this.originalReferences = original.originalReferences;
        this.position = original.position;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public NonRootInputReference clone() {
        return this.clone(true);
    }

    /**
     * @param cloneChangedBit if false, the changed bit will be set to false in
     * the clone. Otherwise the clone will have the same changed bit as this
     * NRIR.
     * @return a clone of this NRIR, where the changed bit may be unset
     */
    public NonRootInputReference clone(final boolean cloneChangedBit) {
        return new NonRootInputReference(this, cloneChangedBit);
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

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(
        final StringBuilder sb,
        final Map<AbstractVariableReference, Integer> varUsers,
        final State stateParam,
        final boolean shortRepresentation)
    {
        super.toString(sb, varUsers, stateParam, shortRepresentation);
        /*
        sb.append('[');
        sb.append(this.position.x.getPos());
        sb.append(':');
        sb.append(this.position.y);
        sb.append(']');
        if (!Globals.DEBUG_NONE) {
            sb.append('(');
            final Iterator<Entry<State, Collection<AbstractVariableReference>>> it =
                this.originalReferences.entrySet().iterator();
            while (it.hasNext()) {
                final Map.Entry<?, ?> entry = it.next();
                sb.append(entry.getKey().hashCode());
                sb.append(":");
                sb.append(entry.getValue());
                if (it.hasNext()) {
                    sb.append(", ");
                }
            }
            sb.append(')');
        }
        */
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public InputRefRootPosition getIRStatePosition(final int frameNum) {
        return NonRootIRPosition.create(this, frameNum);
    }

    /**
     * @param callingState a (calling) state
     * @return true if this input references is used to return to the given
     * state
     */
    public boolean forState(final State callingState) {
        return this.originalReferences.containsKey(callingState);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference getOriginalReference(final State callingState) {
        int standardRefs = 0;
        int nrirRefs = 0;
        final Collection<AbstractVariableReference> nrirInCalling = callingState.getAllNRIRs();
        for (final AbstractVariableReference ref : this.originalReferences.get(callingState)) {
            if (nrirInCalling.contains(ref)) {
                nrirRefs++;
            } else {
                standardRefs++;
            }
        }
        assert (standardRefs <= 1);
        assert (nrirRefs <= 1);
        assert (standardRefs + nrirRefs >= 1);

        assert (this.originalReferences.get(callingState).size() == 1);
        return this.originalReferences.get(callingState).iterator().next();
    }

    /**
     * @param other some other NRIR
     * @return true iff the two NRIRs represent the same set of origin
     * references
     */
    public boolean sameOrigin(final NonRootInputReference other) {
        return this.originalReferences == other.originalReferences;
    }

    /**
     * Mark that this NRIR (also) represents the origRef in callingState.
     * @param callingState a state
     * @param origRef a reference
     */
    public void add(final State callingState, final AbstractVariableReference origRef) {
        if (callingState.addDeletionListener(this)) {
            this.originalReferences.add(callingState, origRef);
        }
    }

    /**
     * We only want to merge NRIRs with another NRIR for the very same position.
     * @param other some NRIR
     * @return true only if we want to merge the NRIRs.
     */
    public boolean mergeOK(final NonRootInputReference other) {
        /*
         * Tt might be a good idea to merge these, to have a finite
         * number of NRIRs even for recursive methods.
         */
        return this.position.equals(other.position);
    }

    /**
     * We cannot merge two NRIRs if the types of the represented values is
     * incompatible (e.g., int vs. Object).
     * @param other some other NRIR
     * @return false if the two NRIRs cannot be merged
     */
    public boolean sameType(final NonRootInputReference other) {
        assert (this != other);

        // do not merge references of incompatible types
        if (this.getReference().pointsToFloat() != other.getReference().pointsToFloat()) {
            return false;
        }
        if (this.getReference().pointsToDouble() != other.getReference().pointsToDouble()) {
            return false;
        }
        if (this.getReference().pointsToInteger() != other.getReference().pointsToInteger()) {
            return false;
        }
        if (this.getReference().pointsToLong() != other.getReference().pointsToLong()) {
            return false;
        }
        if (this.getReference().pointsToReferenceType() != other.getReference().pointsToReferenceType()) {
            return false;
        }

        // long vs. int / double vs. float?
        if (!this.getReference().pointsToReferenceType()) {
            final Boolean wideThis = this.referencesWideNumbers();
            final Boolean wideThat = other.referencesWideNumbers();
            if (wideThis != null && wideThat != null && !wideThis.equals(wideThat)) {
                return false;
            }
        }

        return true;
    }

    /**
     * Asserts that there is no mixup between wide and non-wide.
     * @return true if the original references in the individual states all
     * contain long/double values; false for int/float; null if no original
     * reference exists.
     */
    private Boolean referencesWideNumbers() {
        assert (!this.getReference().pointsToReferenceType());
        Boolean wide = null;
        Boolean nonWide = null;
        for (final Map.Entry<State, Collection<AbstractVariableReference>> entry : this.originalReferences.entrySet()) {
            final Collection<AbstractVariableReference> refs = entry.getValue();
            for (final AbstractVariableReference ref : refs) {
                if (ref.pointsToLong()) {
                    wide = Boolean.TRUE;
                } else {
                    nonWide = Boolean.TRUE;
                }
            }
        }
        /*
         * If this merge construction is correct, we never have a conflict
         * in a single NRIR. For empty original references it is OK that we
         * do not see wide nor non-wide, though.
         */
        assert (wide == null || nonWide == null || !wide || !nonWide);
        return wide;
    }

    /**
     * Remove references to states that do not exist anymore
     * @param states all existing states
     */
    public void clean(final Collection<State> states) {
        this.originalReferences.keySet().retainAll(states);
    }

    /**
     * Merge the information of represented references in the other NRIR into
     * this NRIR. This also updates the "was changed" bit.
     * @param other some other NRIR
     */
    public void add(final NonRootInputReference other) {
        assert (this != other);
        for (final Entry<State, Collection<AbstractVariableReference>> entry : other.originalReferences.entrySet()) {
            if (entry.getKey().addDeletionListener(this)) {
                this.originalReferences.add(entry.getKey(), entry.getValue());
            }
            this.mergeChanges(other.changes);
        }
    }

    /**
     * @param callingState the state calling the invoked method
     * @return the references this NRIR represents in callingState
     */
    public Collection<AbstractVariableReference> getOriginalReferences(final State callingState) {
        return this.originalReferences.get(callingState);
    }

    /**
     * @param callingState the state calling the invoked method
     * @param nrirRef a reference corresponding to this NRIR in callingState
     * @param standardRef a reference corresponding to this NRIR in callingState which is no NRIR
     * @return a pair of NRIRs which both result out of this NRIR. The first entry is a NRIR corresponding to all
     * references except standardRef in callingState. The other entry is a NRIR only corresponding to standardRef in
     * callingState.
     */
    public Pair<NonRootInputReference, NonRootInputReference> split(
        final State callingState,
        final AbstractVariableReference nrirRef,
        final AbstractVariableReference standardRef)
    {
        final NonRootInputReference newNRIR =
            new NonRootInputReference(this.getChanges().copy(), this.getReference(), callingState, nrirRef, this.position);

        // also add the original references for other calling states
        for (final Entry<State, Collection<AbstractVariableReference>> entry : this.originalReferences.entrySet()) {
            final State state = entry.getKey();
            if (state == callingState) {
                continue;
            }
            for (final AbstractVariableReference ref : entry.getValue()) {
                newNRIR.add(state, ref);
            }
        }

        final AbstractVariableReference newRef = AbstractVariableReference.create(this.getReference());
        final NonRootInputReference newNRIRforStandardRef =
            new NonRootInputReference(this.getChanges().copy(), newRef, callingState, standardRef, this.position);

        final Pair<NonRootInputReference, NonRootInputReference> pair = new Pair<>(newNRIR, newNRIRforStandardRef);
        return pair;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void notifyStateDeletion(final State s) {
        this.originalReferences.remove(s);
    }
}
