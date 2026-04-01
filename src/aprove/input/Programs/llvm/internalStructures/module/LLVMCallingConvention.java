package aprove.input.Programs.llvm.internalStructures.module;

import aprove.*;
import immutables.*;

/**
 * LLVM functions, calls and invokes can all have an optional calling convention specified for the call. The calling
 * convention of any pair of dynamic caller/callee must match, or the behavior of the program is undefined.
 * @author CryingShadow
 */
public class LLVMCallingConvention implements Immutable {

    /**
     * The number of the calling convention type CC_N. This value is -1 for all other types.
     */
    private final int number;

    /**
     * The type of the calling convention.
     */
    private final LLVMCallingConventionType type;

    /**
     * @param t The type of the calling convention. Must be different from CC_N.
     */
    public LLVMCallingConvention(LLVMCallingConventionType t) {
        if (Globals.useAssertions) {
            assert (t != LLVMCallingConventionType.CC_N) : "Found CC_N without number!";
            assert (t != null) : "Found empty calling convention type!";
        }
        this.type = t;
        this.number = -1;
    }

    /**
     * Creates a callign convention of type CC_N.
     * @param n The number of the calling convention type CC_N. Must be greater than or equal to 64.
     */
    public LLVMCallingConvention(int n) {
        if (Globals.useAssertions) {
            assert (n >= 64) : "Found CC_N with number less than 64!";
        }
        this.type = LLVMCallingConventionType.CC_N;
        this.number = n;
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof LLVMCallingConvention) {
            final LLVMCallingConvention other = (LLVMCallingConvention)o;
            // just int and enum, so use ==
            return this.number == other.number && this.type == other.type;
        }
        return false;
    }

    /**
     * @return The number of the calling convention type CC_N. This value is -1 for all other types.
     */
    public int getNumber() {
        return this.number;
    }

    /**
     * @return The type of the calling convention.
     */
    public LLVMCallingConventionType getType() {
        return this.type;
    }

    @Override
    public int hashCode() {
        return this.number == -1 ? this.type.hashCode() : 101 * this.number;
    }

    @Override
    public String toString() {
        if (this.number == -1) {
            return this.type.toString();
        } else {
            return this.type.toString() + this.number;
        }
    }

}
