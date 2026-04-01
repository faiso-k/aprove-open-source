package aprove.input.Programs.llvm.internalStructures.memory;

import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import immutables.*;

/**
 * This class represents a range for a pointer to the a recursive data structure on the heap,
 * where we abstract from the length of the structure.
 * @author Jera Hensel
 */
public class LLVMMemoryRecursiveRange extends LLVMMemoryRange {
    
    private final LLVMSimpleTerm length;

    public LLVMMemoryRecursiveRange(LLVMSimpleTerm from, LLVMSimpleTerm to, LLVMType type, LLVMSimpleTerm length) {
        super(from, to, type, false);
        this.length = length;
    }

    public LLVMMemoryRecursiveRange(LLVMSimpleTerm from, LLVMSimpleTerm to, ImmutableList<LLVMType> elemTypes, LLVMSimpleTerm length) {
        super(from, to, new LLVMRecStructureType(elemTypes), false);
        this.length = length;
    }
    
    public ImmutableList<LLVMType> getElemTypes() {
        return ((LLVMRecStructureType)this.getType()).getElementTypes();
    }
    
    public LLVMSimpleTerm getLength() {
        return this.length;
    }
    
    public boolean isContainedIn(ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> heap) {
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : heap.entrySet()) {
            if (entry.getKey() instanceof LLVMMemoryRecursiveRange &&
                this.getFromRef().equals(entry.getKey().getFromRef()) &&
                this.getToRef().equals(entry.getKey().getToRef()) &&
                this.getLength().equals(((LLVMMemoryRecursiveRange)entry.getKey()).getLength())
            ) {
                return true;
            }
        }
        return false;
    }
    
    public LLVMMemoryRecursiveRange setLength(LLVMSimpleTerm length) {
        return new LLVMMemoryRecursiveRange(this.getFromRef(), this.getToRef(), this.getType(), length);
    }

    @Override
    public LLVMMemoryRange replaceReference(LLVMSimpleTerm old, LLVMSimpleTerm replacement) {
        LLVMSimpleTerm new_lower = this.getFromRef();
        LLVMSimpleTerm new_upper = this.getFromRef();
        LLVMSimpleTerm new_length = this.getLength();
        boolean replaced = false;
        if (new_lower == old) {
            new_lower = replacement;
            replaced = true;
        }
        if (new_upper == old) {
            new_upper = replacement;
            replaced = true;
        }
        if (new_length == old) {
            new_length = replacement;
            replaced = true;
        }
        if (!replaced) {
            return null;
        }
        return new LLVMMemoryRecursiveRange(new_lower, new_upper, this.getElemTypes(), new_length);
    }

    @Override
    public String toDOTString() {
        return super.toDOTString() + " -- " + this.length;
    }

    @Override
    public String toString() {
        return super.toString() + "(via " + this.length + ")";
    }

}
