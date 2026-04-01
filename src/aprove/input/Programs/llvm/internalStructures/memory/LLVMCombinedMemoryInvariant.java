package aprove.input.Programs.llvm.internalStructures.memory;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class LLVMCombinedMemoryInvariant implements LLVMMemoryInvariant {
    
    // a mapping from offsets to invariants
    final private Map<BigInteger,LLVMMemoryInvariant> invariants;
    
    private final int hashCode;
    
    public LLVMCombinedMemoryInvariant(Map<BigInteger,LLVMMemoryInvariant> invs) {
        this.invariants = invs;
        this.hashCode = invariants.hashCode();
    }

    @Override
    public int hashCode() {
        return hashCode;
    }
    
    public boolean equals(Object other) {
        if (other == null) {
            return false;
        }
        if (other instanceof LLVMCombinedMemoryInvariant) {
            if (this.invariants == null) {
                return (((LLVMCombinedMemoryInvariant) other).invariants == null);
            }
            for (Map.Entry<BigInteger,LLVMMemoryInvariant> inv : this.invariants.entrySet()) {
                LLVMMemoryInvariant otherInv = ((LLVMCombinedMemoryInvariant) other).getInvariants().get(inv.getKey());
                if (!inv.getValue().equals(otherInv)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }
    
    public LLVMAdditiveChange getChange(BigInteger offset) {
        LLVMMemoryInvariant inv = this.getInvariantWithOffset(offset);
        if (!(inv instanceof LLVMComplexMemoryInvariant)) {
            return null;
        }
        return ((LLVMComplexMemoryInvariant)inv).getChange();
    }
    
    public LLVMMemoryInvariant getInvariantWithOffset(BigInteger offset) {
        return this.invariants.get(offset);
    }
    
    public Map<BigInteger,LLVMMemoryInvariant> getInvariants() {
        return this.invariants;
    }

    public LLVMSimpleTerm getLastRecursivePointer() {
        LLVMSimpleTerm last = null;
        for (LLVMMemoryInvariant inv : this.invariants.values()) {
            if (inv instanceof LLVMComplexMemoryInvariant) {
                LLVMComplexMemoryInvariant compInv = (LLVMComplexMemoryInvariant) inv;
                if (compInv.getType().isPointerType() &&
                        (((LLVMPointerType)compInv.getType()).getTargetType().isStructureType() || ((LLVMPointerType)compInv.getType()).getTargetType() instanceof LLVMNamedType)) {
                    if (last != null) {
                        // we cannot uniquely determine recursive struct pointer
                        return null;
                    }
                    last = compInv.getLastValue();
                }
            }
        }
        return last;
    }
    
    // If there is only one field containing pointers to structs, return the term representing the next pointer.
    public LLVMSimpleTerm getNext() {
        LLVMSimpleTerm next = null;
        for (LLVMMemoryInvariant inv : this.invariants.values()) {
            if (inv instanceof LLVMComplexMemoryInvariant) {
                LLVMComplexMemoryInvariant compInv = (LLVMComplexMemoryInvariant) inv;
                if (compInv.getType().isPointerType() &&
                        (((LLVMPointerType)compInv.getType()).getTargetType().isStructureType() || ((LLVMPointerType)compInv.getType()).getTargetType() instanceof LLVMNamedType)) {
                    if (next != null) {
                        // we cannot uniquely determine recursive struct pointer
                        return null;
                    }
                    next = compInv.getFirstValue();
                }
            }
        }
        return next;
    }

    public BigInteger getOffsetOfRecPointer() {
        BigInteger pointerOffset = null;
        for (Entry<BigInteger, LLVMMemoryInvariant> entry : this.invariants.entrySet()) {
            if (!(entry.getValue() instanceof LLVMComplexMemoryInvariant)) {
                continue;
            }
            LLVMComplexMemoryInvariant inv = (LLVMComplexMemoryInvariant) entry.getValue();
            if (inv.getType().isPointerType() &&
                    (((LLVMPointerType)inv.getType()).getTargetType().isStructureType() || ((LLVMPointerType)inv.getType()).getTargetType() instanceof LLVMNamedType)) {
                if (pointerOffset != null) {
                    // we cannot uniquely determine recursive struct pointer
                    return null;
                }
                pointerOffset = entry.getKey();
            }
        }
        return pointerOffset;
    }

    public LLVMPointerType getTypeOfRecPointer() {
        LLVMPointerType pointerType = null;
        for (Entry<BigInteger, LLVMMemoryInvariant> entry : this.invariants.entrySet()) {
            if (!(entry.getValue() instanceof LLVMComplexMemoryInvariant)) {
                continue;
            }
            LLVMComplexMemoryInvariant inv = (LLVMComplexMemoryInvariant) entry.getValue();
            if (inv.getType().isPointerType() &&
                    (((LLVMPointerType)inv.getType()).getTargetType().isStructureType() || ((LLVMPointerType)inv.getType()).getTargetType() instanceof LLVMNamedType)) {
                if (pointerType != null) {
                    // we cannot uniquely determine recursive struct pointer
                    return null;
                }
                pointerType = (LLVMPointerType) inv.getType();
            }
        }
        return pointerType;
    }

    @Override
    public Set<LLVMSymbolicVariable> getUsedReferences() {
        Set<LLVMSymbolicVariable> refs = new LinkedHashSet<>();
        for (Map.Entry<BigInteger,LLVMMemoryInvariant> inv : this.invariants.entrySet()) {
            refs.addAll(inv.getValue().getUsedReferences());
        }
        return refs;
    }
    
    public LLVMSimpleTerm getValue(BigInteger offset, LLVMType type) {
        LLVMMemoryInvariant inv = this.getInvariantWithOffset(offset);
        if (!(inv instanceof LLVMComplexMemoryInvariant)) {
            return null;
        }
        if (!((LLVMComplexMemoryInvariant)inv).getType().equals(type)) {
            return null;
        }
        return ((LLVMComplexMemoryInvariant)inv).getFirstValue();
    }

    @Override
    public boolean isSimple() {
        return false;
    }

    @Override
    public Pair<LLVMMemoryInvariant, ? extends LLVMAbstractState> joinInvariant(
        LLVMAbstractState state,
        LLVMMemoryInvariant otherInv,
        Abortion aborter
    ) {
        LLVMAbstractState newState = state;
        if (!(otherInv instanceof LLVMCombinedMemoryInvariant)) {
            return null;
        }
        LLVMCombinedMemoryInvariant otherComb = (LLVMCombinedMemoryInvariant) otherInv;
        Map<BigInteger,LLVMMemoryInvariant> newInvariants = new LinkedHashMap<>();
        for (Map.Entry<BigInteger,LLVMMemoryInvariant> inv : this.invariants.entrySet()) {
            BigInteger offset = inv.getKey();
            Pair<LLVMMemoryInvariant,? extends LLVMAbstractState> newInv =
                inv.getValue().joinInvariant(newState, otherComb.getInvariantWithOffset(offset), aborter);
            newState = newInv.getValue();
            newInvariants.put(offset, newInv.getKey());
        }
        return
            new Pair<LLVMMemoryInvariant,LLVMAbstractState>(
                new LLVMCombinedMemoryInvariant(newInvariants),
                newState
            );
    }

    @Override
    public Pair<LLVMSimpleTerm, LLVMAbstractState> load(LLVMAbstractState state, LLVMSimpleTerm ptr,
            LLVMType targetType, boolean unsigned, Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public LLVMMemoryInvariant replaceReference(LLVMSimpleTerm old_ref, LLVMSimpleTerm new_ref) {
        Map<BigInteger,LLVMMemoryInvariant> newInvariants = new LinkedHashMap<>();
        for (Map.Entry<BigInteger,LLVMMemoryInvariant> inv : this.invariants.entrySet()) {
            newInvariants.put(inv.getKey(),inv.getValue().replaceReference(old_ref, new_ref));
        }
        return new LLVMCombinedMemoryInvariant(newInvariants);
    }

    @Override
    public LLVMMemoryInvariant replaceReferences(Map<? extends LLVMSimpleTerm, ? extends LLVMSimpleTerm> map) {
        Map<BigInteger,LLVMMemoryInvariant> newInvariants = new LinkedHashMap<>();
        for (Map.Entry<BigInteger,LLVMMemoryInvariant> inv : this.invariants.entrySet()) {
            newInvariants.put(inv.getKey(),inv.getValue().replaceReferences(map));
        }
        return new LLVMCombinedMemoryInvariant(newInvariants);
    }

    @Override
    public String toString() {
        return this.invariants.toString();
    }

    @Override
    public boolean usesReference(LLVMSimpleTerm other) {
        for (Map.Entry<BigInteger,LLVMMemoryInvariant> inv : this.invariants.entrySet()) {
            if (inv.getValue().usesReference(other)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public Pair<Boolean, ? extends LLVMAbstractState> mayShareWith(LLVMMemoryInvariant other, LLVMAbstractState state,
            Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

}
