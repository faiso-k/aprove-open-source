package aprove.input.Programs.llvm.internalStructures.module;

import aprove.input.Programs.llvm.utils.*;

/**
 * The return type and each parameter of a function type may have a set of parameter attributes associated with them.
 * Parameter attributes are used to communicate additional information about the result or parameters of a function.
 * Parameter attributes are considered to be part of the function, not of the function type, so functions with
 * different parameter attributes can have the same function type.
 * @author Janine Repke, CryingShadow
 */
public enum LLVMParameterAttribute implements LLVMIRExport {

    /**
     * This indicates that the pointer parameter should really be passed by value to the function. The attribute
     * implies that a hidden copy of the pointee is made between the caller and the callee, so the callee is unable to
     * modify the value in the caller. This attribute is only valid on LLVM pointer arguments. It is generally used to
     * pass structs and arrays by value, but is also valid on pointers to scalars. The copy is considered to belong to
     * the caller not the callee (for example, readonly functions should not write to byval parameters). This is not a
     * valid attribute for return values.
     * The byval attribute also supports specifying an alignment with the align attribute. It indicates the alignment
     * of the stack slot to form and the known alignment of the pointer specified to the call site. If the alignment is
     * not specified, then the code generator makes a target-specific assumption.
     */
    BYVAL("byval"),

    /**
     * This indicates that this parameter or return value should be treated in a special target-dependent fashion
     * during while emitting code for a function call or return (usually, by putting it in a register as opposed to
     * memory, though some targets use it to distinguish between two different kinds of registers). Use of this
     * attribute is target-specific.
     */
    INREG("inreg"),

    /**
     * This indicates that the pointer parameter can be excised using the trampoline intrinsics. This is not a valid
     * attribute for return values.
     */
    NEST("nest"),

    /**
     * This indicates that pointer values *based* <pointeraliasing> on the argument or return value do not alias
     * pointer values which are not based on it, ignoring certain "irrelevant" dependencies. For a call to the parent
     * function, dependencies between memory references from before or after the call and from those during the call
     * are "irrelevant" to the noalias keyword for the arguments and return value used in that call. The caller shares
     * the responsibility with the callee for ensuring that these requirements are met. For further details, please see
     * the discussion of the NoAlias response in alias analysis.
     * Note that this definition of noalias is intentionally similar to the definition of restrict in C99 for function
     * arguments, though it is slightly weaker.
     * For function return values, C99's restrict is not meaningful, while LLVM's noalias is.
     */
    NOALIAS("noalias"),

    /**
     * This indicates that the callee does not make any copies of the pointer that outlive the callee itself. This is
     * not a valid attribute for return values.
     */
    NOCAPTURE("nocapture"),

    /** Pointer is known to be not null
     */
    NONNULL("nonnull"),

    /** Pointer is known to be written to
     */
    READONLY("readonly"),

    /**
     * This indicates to the code generator that the parameter or return value should be sign-extended to the extent
     * required by the target's ABI (which is usually 32-bits) by the caller (for a parameter) or the callee (for a
     * return value).
     */
    SIGNEXT("signext"),

    /**
     * This indicates that the pointer parameter specifies the address of a structure that is the return value of the
     * function in the source program. This pointer must be guaranteed by the caller to be valid: loads and stores to
     * the structure may be assumed by the callee to not to trap and to be properly aligned. This may only be applied
     * to the first parameter. This is not a valid attribute for return values.
     */
    SRET("sret"),

    /**
     * This indicates to the code generator that the parameter or return value should be zero-extended to the extent
     * required by the target's ABI (which is usually 32-bits, but is 8-bits for a i1 on x86-64) by the caller (for a
     * parameter) or the callee (for a return value).
     */
    ZEROEXT("zeroext");

    /**
     * The name of this parameter attribute.
     */
    private final String name;

    /**
     * @param n The name of this parameter attribute.
     */
    private LLVMParameterAttribute(final String n) {
        this.name = n;
    }

    @Override
    public String toString() {
        return this.name;
    }

    @Override
    public String toLLVMIR() {
        return this.name;
    }

}
