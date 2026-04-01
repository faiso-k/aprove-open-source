package aprove.input.Programs.llvm.internalStructures.memory;

import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public interface LLVMMemoryInvariant extends Immutable {

    @Override
    public abstract boolean equals(Object obj);

    public abstract Set<LLVMSymbolicVariable> getUsedReferences();

    @Override
    public abstract int hashCode();

    public abstract boolean isSimple();

    public abstract Pair<LLVMMemoryInvariant, ? extends LLVMAbstractState> joinInvariant(
        LLVMAbstractState newState,
        LLVMMemoryInvariant otherInv,
        Abortion aborter
    );

    /**
     * @param state The state in which this invariant holds.
     * @param ptr The pointer to load.
     * @param targetType The target type of the pointer.
     * @param unsigned Is the target type unsigned?
     * @return The specified state possibly updated during checks and the loaded value.
     */
    public abstract Pair<LLVMSimpleTerm, LLVMAbstractState> load(
        LLVMAbstractState state,
        LLVMSimpleTerm ptr,
        LLVMType targetType,
        boolean unsigned,
        Abortion aborter
    );

    public abstract LLVMMemoryInvariant replaceReference(LLVMSimpleTerm old_ref, LLVMSimpleTerm new_ref);

    public abstract LLVMMemoryInvariant replaceReferences(Map<? extends LLVMSimpleTerm, ? extends LLVMSimpleTerm> map);

    @Override
    public abstract String toString();

    public abstract boolean usesReference(LLVMSimpleTerm other);

    /**
     * @return A boolean flag and a state. The flag is false iff we can prove that the two invariants cannot contain
     *         common elements (e.g., value ranges are disjoint). This is used to infer that two ranges cannot be be
     *         intersecting. The state is the specified one possibly updated during checks.
     */
    Pair<Boolean, ? extends LLVMAbstractState> mayShareWith(LLVMMemoryInvariant other, LLVMAbstractState state, Abortion aborter);

}
