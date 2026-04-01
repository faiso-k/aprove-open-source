package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;
import java.util.function.BiFunction;

import aprove.Globals;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * A single input reference is used to create a connection between a standard
 * AbstractVariableReference x in a state A and some corresponding reference y
 * in some other state B, where B called the method of A. When now returning
 * from A and continuing in B, the input reference is used to update the
 * information visible from y in B so that changes (side effects?) to x in A are
 * regarded properly. Even if no change occurred, refined information can be
 * used to also refine the information in B (using intersection).
 * <p>
 * There are two kinds of input references. For arguments we just store a (root)
 * position in the calling state which enables us to find the connection. For
 * references that may be changed due to side effects in the called method just
 * due to some (possible) sharing with the arguments, we store information about
 * the original state and the reference name within.
 * <p>
 * The boolean flag is used to denote if the referenced value (or anything
 * reachable from that) was changed.
 * @author cotto
 */
public abstract class InputReference {

    IRChangeInformations changes = new IRChangeInformations();

    /**
     * The reference we are dealing with.
     */
    private AbstractVariableReference reference;

    /**
     * @param b true iff the stored information visible from the reference was
     * changed.
     * @param ref the reference we are dealing with
     */
    public InputReference(final AbstractVariableReference ref) {
        this.reference = ref;
    }

    protected InputReference(final InputReference original) {
        this.reference = original.reference;
        this.changes = original.changes.copy();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public abstract InputReference clone();

    /**
     * @return false only if no value visible from the associated reference was
     * changed.
     */
    public boolean getChanged() {
        return changes.changed();
    }

    public IRChangeInformations getChanges() {
        return changes;
    }

    protected void setChanges(IRChangeInformations changes) {
        this.changes = changes;
    }

    public boolean containsChanges(IRChangeInformations other) {
        return changes.containsChanges(other);
    }

    public boolean containsChanges(IRChangeInformations other, BiFunction<AbstractVariableReference, AbstractVariableReference, Boolean> varComparator) {
        return changes.containsChanges(other, varComparator);
    }

    public boolean mergeChanges(IRChangeInformations other) {
        return this.changes.merge(other);
    }

    public boolean mergeChanges(IRChangeInformations other, VariableCache varCache) {
        return this.changes.merge(other, varCache);
    }

    /**
     * @param callingState the state that caused this input reference to exist
     * @return the corresponding reference in the calling state
     */
    public abstract AbstractVariableReference getOriginalReference(State callingState);

    /**
     * @return the reference
     */
    public AbstractVariableReference getReference() {
        return this.reference;
    }

    /**
     * Rename the reference.
     * @param oldRef the old name
     * @param newRef the new name
     * @return true iff this IR was changed
     */
    public boolean replaceReference(final AbstractVariableReference oldRef, final AbstractVariableReference newRef) {
        changes.replaceReference(oldRef, newRef);
        if (this.reference.equals(oldRef)) {
            this.replaceReference(newRef);
            return true;
        }
        return false;
    }

    /**
     * Rename the reference.
     * @param newRef the new name
     */
    public void replaceReference(final AbstractVariableReference newRef) {
        if (newRef.isNULLRef()) {
            changes.clear();
        }
        this.reference = newRef;
    }

    public void putLocalChange(IrChangeInformation changeInformation, FieldIdentifier field) {
        changes.putLocalChange(changeInformation, field);
    }

    public void addReachableChange(IrChangeInformation change) {
        changes.addReachableChange(change, null);
    }

    /**
     * @param sb a string builder
     * @param varUsers a map giving information about the number of places the
     * given reference is used.
     * @param shortRepresentation if some value only occurs at a single
     * position, show the value instead of the reference
     * @param state the state containing this input reference
     */
    public void toString(
        final StringBuilder sb,
        final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean shortRepresentation)
    {
        if (this.getChanged()) {
            if (Globals.DEBUG_THIES) {
                sb.append(changes);
            } else {
                sb.append('!');
            }
        }
        if (varUsers != null && state != null) {
            sb.append(PrettyVariablePrinter.prettyPrint(this.reference, varUsers, state, shortRepresentation));
        } else {
            sb.append(this.reference.toString());
        }
    }

    /**
     * @param frameNum the position of the stack frame containing this IR (most
     * of the times this is 0)
     * @return a state position object that also can be used to find the
     * corresponding (input) reference in some other state.
     */
    public abstract InputRefRootPosition getIRStatePosition(int frameNum);
}
