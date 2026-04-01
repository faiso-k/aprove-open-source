package aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation;

import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * IrChangeInformation is immutable.
 */
public abstract class IrChangeInformation {

    public static enum ChangeType{
        ADDRESS,
        INTEGER,
        FLOAT;
    }

    public abstract IrChangeInformation merge(IrChangeInformation other, VariableCache varCache);

    public abstract ChangeType getChangeType();

    public abstract boolean containsChange(IrChangeInformation other, BiFunction<AbstractVariableReference, AbstractVariableReference, Boolean> varComparator);

    public abstract IrChangeInformation asChangeFromLowerFrame();

    public IrChangeInformation replaceReference(VariableCache varCache, boolean left) {
        return replaceReference(curRef -> {
            Set<AbstractVariableReference> results = varCache.getResults(curRef, left);
            if (results.size() == 1) {
                return results.iterator().next();
            } else {
                return null;
            }
        });
    }

    public IrChangeInformation replaceReference(AbstractVariableReference oldRef, AbstractVariableReference newRef) {
        return replaceReference(curRef -> curRef == oldRef ? newRef : curRef);
    }

    public abstract IrChangeInformation replaceReference(Function<AbstractVariableReference, AbstractVariableReference> replacer);

    @Override
    public abstract int hashCode();

    @Override
    public abstract boolean equals(Object obj);

    public static IrChangeInformation create(HeapPositions heapPos, AbstractVariableReference objectRef,
            AbstractVariableReference newValue, AbstractVariableReference oldValue) {
        if (newValue.pointsToReferenceType()) {
            return new IrAddressChangeInformation(heapPos, objectRef, newValue, oldValue);
        } else {
            AbstractNumber newNumber = (AbstractNumber)heapPos.getState().getAbstractVariable(newValue);
            return new IrPrimitiveChangeInformation(newNumber);
        }
    }

    public static IrChangeInformation create(HeapPositions heapPos, FieldIdentifier staticField,
            AbstractVariableReference newValue, AbstractVariableReference oldValue) {
        if (newValue.pointsToReferenceType()) {
            return new IrAddressChangeInformation(heapPos, staticField, newValue, oldValue);
        } else {
            AbstractNumber newNumber = (AbstractNumber)heapPos.getState().getAbstractVariable(newValue);
            return new IrPrimitiveChangeInformation(newNumber);
        }
    }
}
