package aprove.input.Programs.llvm.internalStructures.literals;

import java.math.BigInteger;

import aprove.input.Programs.llvm.internalStructures.dataType.*;

/**
 * Class representing an integer value with maximum size of 64 bits. For bigger integer values use BigInt.
 * @author Janine Repke, CryingShadow
 */
public class LLVMRegularIntLiteral extends LLVMIntLiteral {

    /**
     * If value has left bounds, push it back into its bounds. Since this is a literal, it is always treated as bounded.
     * @param type The type defining the bounds.
     * @param val The value to adjust.
     * @return The appropriate value in its type bounds.
     */
    private static long pushIntoBounds(LLVMType type, long val, boolean unsigned) {
        long lower = type.getIntegerType(unsigned, true).getLower().getConstant().longValue();
        long upper = type.getIntegerType(unsigned, true).getUpper().getConstant().longValue();
        if ((lower <= val) && (upper >= val)) {
            // value is in the interval of its type
            return val;
        } else {
            // we have to compute the correct value
            long newVal = val;
            long size = upper - lower + 1;
            while (lower > newVal) {
                newVal = newVal + size;
            }
            while (upper < newVal) {
                newVal = newVal - size;
            }
            return newVal;
        }
    }

    /**
     * The value.
     */
    private final long value;

    /**
     * @param type The type (must be BasicIntType).
     * @param val The value.
     */
    public LLVMRegularIntLiteral(LLVMType type, long val, boolean unsigned) {
        super(type);
        // type is checked in super constructor
        this.value = LLVMRegularIntLiteral.pushIntoBounds(type, val, unsigned);
    }

    /**
     * @param bitwidth The bitwidth.
     * @param val The value.
     * @param unsigned Is this literal unsigned?
     */
    public LLVMRegularIntLiteral(int bitwidth, long val, boolean unsigned) {
        this(new LLVMIntType(bitwidth), val, unsigned);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof LLVMRegularIntLiteral) {
            return (((LLVMRegularIntLiteral) obj).value == this.value);
        }
        return false;
    }

    @Override
    public BigInteger getValueAsBigInteger() {
        return BigInteger.valueOf(this.value);
    }

    @Override
    public long getValueAsLong() {
        return this.value;
    }

    @Override
    public int hashCode() {
        return Long.valueOf(this.value).hashCode();
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("BasicInt value: ");
        strBuilder.append(this.value);
        return strBuilder.toString();
    }

    @Override
    public int toInt() throws UnsupportedOperationException {
        return (int)this.getValueAsLong();
    }

    @Override
    public String toString() {
        return String.valueOf(this.value);
    }

    @Override
    public String toLLVMIR() {
        return String.valueOf(this.value);
    }

}
