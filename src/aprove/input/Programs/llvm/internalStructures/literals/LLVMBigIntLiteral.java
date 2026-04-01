package aprove.input.Programs.llvm.internalStructures.literals;

import java.math.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMBigIntLiteral extends LLVMIntLiteral {

    /**
     * The value.
     */
    private final BigInteger value;

    /**
     * @param type The type (must be BasicIntType of a bitwidth bigger than 64).
     * @param value The value.
     */
    public LLVMBigIntLiteral(LLVMType type, BigInteger value) {
        super(type);
        if (Globals.useAssertions) {
            // type.isIntType() is checked in super constructor
            assert (type.getThisAsIntType().size() >= 64) : "Type is not suitable for BasicBigInt!";
        }
        this.value = value;
    }

    /**
     * @param type The type (must be BasicIntType of a bitwidth bigger than 64).
     * @param valueRep A String containing the representation of the value.
     */
    public LLVMBigIntLiteral(LLVMType type, String valueRep) {
        super(type);
        if (Globals.useAssertions) {
            // type.isIntType() is checked in super constructor
            assert (type.getThisAsIntType().size() >= 64) : "Type is not suitable for BasicBigInt!";
        }
        this.value = new BigInteger(valueRep);
    }

    /**
     * @param bitSize The bitwidth of the value (must be bigger than 64).
     * @param valueRep A String containing the representation of the value.
     */
    public LLVMBigIntLiteral(int bitSize, String valueRep) {
        this(new LLVMIntType(bitSize), valueRep);
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
        final LLVMBigIntLiteral other = (LLVMBigIntLiteral)obj;
        if (!this.getType().equals(other.getType())) {
            return false;
        }
        if (this.value == null) {
            if (other.value != null) {
                return false;
            }
        } else if (!this.value.equals(other.value)) {
            return false;
        }
        return true;
    }

    /**
     * @return The value.
     */
    @Override
    public BigInteger getValueAsBigInteger() {
        return this.value;
    }

    @Override
    public long getValueAsLong() {
        if (this.value.bitLength() > 63) {
            throw new NumberFormatException("Value is not representable as long!");
        }
        return this.value.longValue();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.getType() == null) ? 0 : this.getType().hashCode());
        result = prime * result + ((this.value == null) ? 0 : this.value.hashCode());
        return result;
    }

    @Override
    public String toDebugString() {
        final StringBuilder strBuilder = new StringBuilder("BasicBigInt");
        if (this.value != null) {
            strBuilder.append(" valueRep: " + this.value + " type: " + this.getType());
        }
        return strBuilder.toString();
    }

    @Override
    public int toInt() throws UnsupportedOperationException {
        return this.getValueAsBigInteger().intValue();
    }

    @Override
    public String toString() {
        return this.value.toString();
    }

}
