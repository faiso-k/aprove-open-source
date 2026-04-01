package aprove.input.Programs.llvm.internalStructures.dataType;

import java.math.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntegerReasoning.*;

/**
 * Pointer type.
 * @author Janine Repke, CryingShadow
 */
public class LLVMPointerType extends LLVMType {

    /**
     * @param size The size of the pointer type.
     * @param useBoundedIntegers Use bounded integers?
     * @return The corresponding integer type for a pointer type of the specified size.
     */
    public static IntegerType getIntegerType(int size, boolean useBoundedIntegers) {
        if (useBoundedIntegers) {
            switch (size) {
                case 16:
                    return IntegerType.UI16;
                case 32:
                    return IntegerType.UI32;
                case 64:
                    return IntegerType.UI64;
                default:
                    throw new UnsupportedOperationException("Pointer type of target architecture not supported!");
            }
        }
        return IntegerType.UNBOUND_NON_NEGATIVE;
    }

    /**
     * @param pointerSize The pointer size.
     * @return An i8* pointer type with the specified pointer size.
     */
    public static LLVMPointerType i8star(int pointerSize) {
        return new LLVMPointerType(LLVMIntType.I8, pointerSize, null);
    }

    /**
     * The address space (TODO non-null - default address space is zero).
     */
    private final LLVMLiteral addressSpace;

    /**
     * The size of a pointer in bits.
     */
    private final int size;

    /**
     * The type of the value the pointer is pointing to.
     */
    private final LLVMType targetType;

    /**
     * @param pointedToType The type of the value the pointer is pointing to.
     * @param pointerSize The size of a pointer in bits.
     * @param addrSpace The address space.
     */
    public LLVMPointerType(LLVMType pointedToType, int pointerSize, LLVMLiteral addrSpace) {
        if (Globals.useAssertions) {
            assert (pointerSize > 0) : "Pointer type of non-positive size found!";
        }
        this.targetType = pointedToType;
        this.size = pointerSize;
        this.addressSpace = addrSpace;
    }

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) {
        return new LLVMNullLiteral(this);
        // TODO check whether null or void would be better here
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof LLVMPointerType)) {
            return false;
        }
        LLVMPointerType other = (LLVMPointerType) obj;
        if (this.addressSpace == null) {
            if (other.addressSpace != null) {
                return false;
            }
        } else if (!this.addressSpace.equals(other.addressSpace)) {
            return false;
        }
        if (this.targetType == null) {
            if (other.targetType != null) {
                return false;
            }
        } else if (!this.targetType.equals(other.targetType)) {
            return false;
        }
        if (this.size != other.size) {
            return false;
        }
        return true;
    }

    /**
     * @return The address space.
     */
    public LLVMLiteral getAddressSpace() {
        return this.addressSpace;
    }

    @Override
    public AbstractBoundedInt getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        return AbstractBoundedInt.getUnknown(this.getIntegerType(unsigned, useBoundedIntegers));
    }

    @Override
    public IntegerType getIntegerType(boolean unsigned, boolean useBoundedIntegers) {
        return LLVMPointerType.getIntegerType(this.size, useBoundedIntegers);
    }

    /**
     * @return The type of the value the pointer is pointing to.
     */
    public LLVMType getTargetType() {
        return this.targetType;
    }

    @Override
    public LLVMPointerType getThisAsPointerType() {
        return this;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.addressSpace == null) ? 0 : this.addressSpace.hashCode());
        result = prime * result + ((this.targetType == null) ? 0 : this.targetType.hashCode());
        return result;
    }

    @Override
    public boolean isPointerType() {
        return true;
    }
    
    public boolean pointsToStruct() {
        return this.getTargetType().isStructureType() || this.getTargetType() instanceof LLVMNamedType;
    }

    @Override
    public LLVMType setSizes(int pointerSize) {
        return new LLVMPointerType(this.getTargetType().setSizes(pointerSize), pointerSize, null);
    }

    @Override
    public int size() {
        return this.size;
    }

    /**
     * @return The offset necessary for a legal memory access with this pointer type.
     */
    public BigInteger toOffset() {
        return BigInteger.valueOf(IntegerUtils.bitsToBytes(this.getTargetType().size()) - 1);
    }

    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder("*");
        strBuilder.append(this.targetType.toString());
        if (this.addressSpace != null) {
            strBuilder.append(" addressSpace: " + this.addressSpace);
        }
        return strBuilder.toString();
    }

}
