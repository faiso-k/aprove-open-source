package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;

/**
 * Represents represents a 32-bit floating point value.
 * @author Janine Repke, CryingShadow
 */
public class LLVMFloatLiteral extends LLVMLiteral {

    public static LLVMFloatLiteral UNKNOWN;
    
    /**
     * The value.
     */
    private final float value;

    /**
     * @param type The type (must be a float type).
     * @param val The value.
     */
    public LLVMFloatLiteral(LLVMType type, float val) {
        super(type);
        if (Globals.useAssertions) {
            assert (type.getFirstNonNamedType() instanceof LLVMFloatType) : "Float is no float!";
        }
        this.value = val;
    }

    /**
     * @param valueParam The value.
     */
    public LLVMFloatLiteral(float valueParam) {
        this(new LLVMFloatType(), valueParam);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof LLVMFloatLiteral) {
            final LLVMFloatLiteral basicFloat = (LLVMFloatLiteral) obj;
            return (this.value == basicFloat.value);
        }
        return false;
    }

    /**
     * @return The value.
     */
    public float getValue() {
        return this.value;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + Float.floatToIntBits(this.value);
        return result;
    }

    @Override
    public String toDebugString() {
        final String str = "BasicFloatName value: " + this.value;
        return str;
    }

    @Override
    public String toString() {
        return String.valueOf(this.value);
    }

}
