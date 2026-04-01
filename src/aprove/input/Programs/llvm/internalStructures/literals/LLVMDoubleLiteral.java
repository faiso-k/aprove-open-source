package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;

/**
 * Represents a 64-bit floating point value.
 * @author Janine Repke, CryingShadow
 */
public class LLVMDoubleLiteral extends LLVMLiteral {

    /**
     * The value.
     */
    private final double value;

    /**
     * @param type The type (must be a double type).
     * @param val The value.
     */
    public LLVMDoubleLiteral(LLVMType type, double val) {
        super(type);
        if (Globals.useAssertions) {
            assert (type.getFirstNonNamedType() instanceof LLVMDoubleType) : "Double is no double!";
        }
        this.value = val;
    }

    /**
     * @param valueParam The value.
     */
    public LLVMDoubleLiteral(double valueParam) {
        this(new LLVMDoubleType(), valueParam);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof LLVMDoubleLiteral) {
            return (this.value == ((LLVMDoubleLiteral) obj).value);
        } else {
            return false;
        }
    }

    /**
     * @return The value.
     */
    public double getValue() {
        return this.value;
    }

    @Override
    public int hashCode() {
        final int prime = 43;
        int result = 5;
        long temp;
        temp = Double.doubleToLongBits(this.value);
        result = prime * result + (int) (temp ^ (temp >>> 32));
        return result;
    }

    @Override
    public String toDebugString() {
        final String str = "BasicDoubleName value: " + this.value;
        return str;
    }

    @Override
    public String toString() {
        return String.valueOf(this.value);
    }

}
