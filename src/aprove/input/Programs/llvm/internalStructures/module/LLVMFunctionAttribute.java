package aprove.input.Programs.llvm.internalStructures.module;

import aprove.*;
import immutables.*;

/**
 * Function attributes are set to communicate additional information about a function. Function attributes are
 * considered to be part of the function, not of the function type, so functions with different function attributes can
 * have the same function type.
 * @author CryingShadow
 */
public class LLVMFunctionAttribute implements Immutable {

    /**
     * Allows to specify the alignstack number for ALIGNSTACK_N. This attribute
     * is not relevant for all other options and will be -1 then.
     */
    private final int number;

    /**
     * The type of the function attribute.
     */
    private final LLVMFunctionAttributeType type;

    /**
     * @param t The type of the function attribute (must be different from ALIGNSTACK_N).
     */
    public LLVMFunctionAttribute(LLVMFunctionAttributeType t) {
        if (Globals.useAssertions) {
            assert (t != LLVMFunctionAttributeType.ALIGNSTACK_N) : "Found ALIGNSTACK_N without number!";
            assert (t != null) : "Found function attribute with empty type!";
        }
        this.type = t;
        this.number = -1;
    }

    /**
     * Creates an ALIGNTACK_N FunctionAttribute with the specified number.
     * @param n The alignstack number for ALIGNSTACK_N.
     */
    public LLVMFunctionAttribute(int n) {
        this.type = LLVMFunctionAttributeType.ALIGNSTACK_N;
        this.number = n;
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof LLVMFunctionAttribute) {
            final LLVMFunctionAttribute other = (LLVMFunctionAttribute)o;
            // just int and enum, so use ==
            return this.number == other.number && this.type == other.type;
        }
        return false;
    }

    /**
     * @return The alignstack number for ALIGNSTACK_N.
     */
    public int getNumber() {
        return this.number;
    }

    /**
     * @return The type of the function attribute.
     */
    public LLVMFunctionAttributeType getType() {
        return this.type;
    }

    @Override
    public int hashCode() {
        return this.number == -1 ? this.type.hashCode() : 97 * this.number;
    }

    @Override
    public String toString() {
        if (this.number == -1) {
            return this.type.toString();
        } else {
            return this.type.toString() + this.number + ")";
        }
    }

}
