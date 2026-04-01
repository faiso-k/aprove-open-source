package aprove.input.Programs.llvm.internalStructures.dataType;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMIntType extends LLVMType {

    /**
     * The type i1.
     */
    public static final LLVMIntType I1 = new LLVMIntType(1);

    /**
     * The type i32.
     */
    public static final LLVMIntType I32 = new LLVMIntType(32);

    /**
     * The type i64.
     */
    public static final LLVMIntType I64 = new LLVMIntType(64);

    /**
     * The type i8.
     */
    public static final LLVMIntType I8 = new LLVMIntType(8);

    /**
     * The bit-width of this integer type.
     */
    private final int numberOfBits;

    /**
     * @param numberOfBitsParam The bit-width of this integer type.
     */
    public LLVMIntType(int numberOfBitsParam) {
        if (Globals.useAssertions) {
            assert (numberOfBitsParam >= 0) : "The number of bits of an integer type must be non-negative!";
        }
        this.numberOfBits = numberOfBitsParam;
    }

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) {
        return new LLVMRegularIntLiteral(this.numberOfBits, 0, unsigned);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final LLVMIntType other = (LLVMIntType)obj;
        if (this.numberOfBits != other.numberOfBits) {
            return false;
        }
        return this.size() == other.size();
    }

    @Override
    public AbstractBoundedInt getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        return AbstractBoundedInt.getUnknown(this.getIntegerType(unsigned, useBoundedIntegers));
    }

    @Override
    public IntegerType getIntegerType(boolean unsigned, boolean useBoundedIntegers) {
        if (useBoundedIntegers) {
            if (unsigned) {
                switch (this.size()) {
                    case 1: return IntegerType.I1;
                    case 8: return IntegerType.UI8;
                    case 16: return IntegerType.UI16;
                    case 32: return IntegerType.UI32;
                    case 64: return IntegerType.UI64;
                    default:
                        return new IntegerType(this.size(), true);
                }
            } else {
                switch (this.size()) {
                    case 1: return IntegerType.I1;
                    case 8: return IntegerType.I8;
                    case 16: return IntegerType.I16;
                    case 32: return IntegerType.I32;
                    case 64: return IntegerType.I64;
                    default:
                        return new IntegerType(this.size(), true);
                }
            }
        }
        return IntegerType.UNBOUND;
    }

    @Override
    public LLVMIntType getThisAsIntType() {
        return this;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.numberOfBits;
        return result;
    }

    @Override
    public boolean isBooleanOrVecOfBooleanType() {
        return this.isBooleanType();
    }

    @Override
    public boolean isBooleanType() {
        // represents a boolean if the number of bits is one
        return this.numberOfBits == 1;
    }

    @Override
    public boolean isIntOrVecOfIntType() {
        return true;
    }

    @Override
    public boolean isIntType() {
        return true;
    }

    @Override
    public boolean isIntTypeOfSize(int size) {
        return this.size() == size;
    }

    @Override
    public int size() {
        return this.numberOfBits;
    }

    @Override
    public String toString() {
        //String str = "BasicIntType(" + numberOfBits + ")";
        return "i" + this.numberOfBits;
    }

    @Override
    public String toLLVMIR() {
        return "i" + this.numberOfBits;
    }

}
