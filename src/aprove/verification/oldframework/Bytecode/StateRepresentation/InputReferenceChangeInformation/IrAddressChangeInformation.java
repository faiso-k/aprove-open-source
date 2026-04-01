package aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation;

import java.util.function.BiFunction;
import java.util.function.Function;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

public class IrAddressChangeInformation extends IrChangeInformation {

    public static IrAddressChangeInformation UNKNOWN = new IrAddressChangeInformation();

    private boolean newSuccOfOld = false; //special case where the new child ref was reachable from the old child, i.e. when deleting in a list
    private AbstractVariableReference writtenRef;
    private StatePosition writePosition;
    private StatePosition changeFromLowerFrame;

    IrAddressChangeInformation(HeapPositions heapPos, FieldIdentifier staticField,
            AbstractVariableReference newValue, AbstractVariableReference oldValue) {
        //TODO extract method to remove duplicate code
        State state = heapPos.getState();
        this.writtenRef = newValue;
        this.writePosition = StaticFieldRootPosition.create(staticField);

        if (oldValue != null && !oldValue.isNULLRef()) {
            /*
             * Special Case: New Value is a successor of the old value
             */
            if (Reachability.getReachableRefs(oldValue, false, state).contains(newValue)) {
                newSuccOfOld = true;
                writtenRef = null;
            }
        }
    }

    IrAddressChangeInformation(HeapPositions heapPos, AbstractVariableReference objectRef,
            AbstractVariableReference newValue, AbstractVariableReference oldValue) {
        State state = heapPos.getState();
        this.writtenRef = newValue;
        this.writePosition = heapPos.getShortestPositionForRef(objectRef);

        if (oldValue != null && !oldValue.isNULLRef()) {
            /*
             * Special Case: New Value is a successor of the old value
             */
            if (Reachability.getReachableRefs(oldValue, false, state).contains(newValue)) {
                newSuccOfOld = true;
                writtenRef = null;
            }
        }
    }

    private IrAddressChangeInformation() {}

    private IrAddressChangeInformation(IrAddressChangeInformation original) {
        this.newSuccOfOld = original.newSuccOfOld;
        this.writtenRef = original.writtenRef;
        this.writePosition = original.writePosition;
        this.changeFromLowerFrame = original.changeFromLowerFrame;
    }

    public IrAddressChangeInformation(IrAddressChangeInformation first, IrAddressChangeInformation second, VariableCache varCache) {
        this.newSuccOfOld = first.newSuccOfOld && second.newSuccOfOld;
        if (first.writtenRef != null && second.writtenRef != null) {
            if (varCache != null) { //TODO check if varCache contains entries for nullref and for the case where both refs are equal
                this.writtenRef = varCache.get(first.writtenRef, second.writtenRef);
            } else if (first.writtenRef.equals(second.writtenRef)) {
                this.writtenRef = first.writtenRef;
            }
        }
        if (first.writePosition == second.writePosition)
            this.writePosition = first.writePosition;
        if (first.changeFromLowerFrame == second.changeFromLowerFrame)
            this.changeFromLowerFrame = first.changeFromLowerFrame;
    }

    public boolean isNullWrite() {
        return this.writtenRef != null && this.writtenRef.isNULLRef();
    }

    public boolean isNewSuccOfOld() {
        return newSuccOfOld;
    }

    public AbstractVariableReference getWrittenRef() {
        return writtenRef;
    }

    public StatePosition getWritePosition() {
        return writePosition;
    }

    public boolean isChangeFromLowerFrame() {
        return changeFromLowerFrame != null;
    }

    public StatePosition getChangeFromLowerFrame() {
        return changeFromLowerFrame;
    }

    @Override
    public IrAddressChangeInformation asChangeFromLowerFrame() {
        IrAddressChangeInformation res = new IrAddressChangeInformation(this);
        res.writtenRef = null;
        res.writePosition = null;
        if (this.changeFromLowerFrame == null && !this.newSuccOfOld) { //TODO I do not like this, can we get rid of newSuccOfOld
            res.changeFromLowerFrame = this.writePosition;
        } //otherwise the copy constructor already copied this.ChangeFromLowerFrame to res
        return res;
    }

    @Override
    public boolean containsChange(IrChangeInformation other, BiFunction<AbstractVariableReference, AbstractVariableReference, Boolean> varComparator) {
        if (!(other instanceof IrAddressChangeInformation)) {
            assert false;
            return false;
        }
        IrAddressChangeInformation otherCh = (IrAddressChangeInformation) other;
        if (this.newSuccOfOld && !otherCh.newSuccOfOld) {
            return false;
        }
        if (this.writtenRef != null) {
            if (otherCh.writtenRef == null)
                return false;
            else if (!varComparator.apply(this.writtenRef, otherCh.writtenRef)) {
                return false;
            }
        }
        if (this.writePosition != null && this.writePosition != otherCh.writePosition) { //TODO check if this makes sense when less tired
            return false;
        }
        if (this.changeFromLowerFrame != null && this.changeFromLowerFrame != otherCh.changeFromLowerFrame) {
            return false;
        }
        return true;
    }

    @Override
    public ChangeType getChangeType() {
        return ChangeType.ADDRESS;
    }

    @Override
    public IrAddressChangeInformation merge(IrChangeInformation other, VariableCache varCache) {
        if (varCache == null && this.containsChange(other, (var1, var2) -> var1 == var2))
            return this;
        if (varCache != null && this.containsChange(other, varCache::contains))
            return this;
        if (other instanceof IrAddressChangeInformation)
            return new IrAddressChangeInformation(this, (IrAddressChangeInformation) other, varCache);
        assert false;
        return null;
    }

    @Override
    public IrChangeInformation replaceReference(Function<AbstractVariableReference, AbstractVariableReference> replacer) {
        if (writtenRef == null)
            return this;
        AbstractVariableReference newRef = replacer.apply(writtenRef);
        if (newRef == writtenRef)
            return this;
        IrAddressChangeInformation res = new IrAddressChangeInformation(this);
        res.writtenRef = newRef;
        return res;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((changeFromLowerFrame == null) ? 0 : changeFromLowerFrame.hashCode());
        result = prime * result + (newSuccOfOld ? 1231 : 1237);
        result = prime * result + ((writePosition == null) ? 0 : writePosition.hashCode());
        result = prime * result + ((writtenRef == null) ? 0 : writtenRef.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        IrAddressChangeInformation other = (IrAddressChangeInformation) obj;
        if (changeFromLowerFrame == null) {
            if (other.changeFromLowerFrame != null)
                return false;
        } else if (!changeFromLowerFrame.equals(other.changeFromLowerFrame))
            return false;
        if (newSuccOfOld != other.newSuccOfOld)
            return false;
        if (writePosition == null) {
            if (other.writePosition != null)
                return false;
        } else if (!writePosition.equals(other.writePosition))
            return false;
        if (writtenRef == null) {
            if (other.writtenRef != null)
                return false;
        } else if (!writtenRef.equals(other.writtenRef))
            return false;
        return true;
    }

    @Override
    public String toString() {
        if (isNullWrite())
            return "nullWrite";
        if (isNewSuccOfOld())
            return "newSuccOfOld";
        if (isChangeFromLowerFrame())
            return "changeFromLowerFrame(" + changeFromLowerFrame + ")";
        if (writtenRef != null)
            return writtenRef.toString() + "|" + writePosition.toString();
        return "unknown";
    }
}
