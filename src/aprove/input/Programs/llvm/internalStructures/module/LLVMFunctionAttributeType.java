package aprove.input.Programs.llvm.internalStructures.module;

/**
 * Function attributes are set to communicate additional information about a function. Function attributes are
 * considered to be part of the function, not of the function type, so functions with different function attributes can
 * have the same function type.
 * @author Janine Repke, CryingShadow
 */
public enum LLVMFunctionAttributeType {

    /**
     * This attribute indicates that the address safety analysis is enabled for this function.
     */
    ADDRESS_SAFETY("address_safety"),

    /**
     * This attribute indicates that, when emitting the prologue and epilogue, the backend should forcibly align the
     * stack pointer. Specify the desired alignment, which must be a power of two, in parentheses.
     * The number is specified outside this enum.
     */
    ALIGNSTACK_N("alignstack("),

    /**
     * This attribute indicates that the inliner should attempt to inline this function into callers whenever possible,
     * ignoring any active inlining size threshold for this caller.
     */
    ALWAYSINLINE("alwaysinline"),

    /**
     * This attribute indicates that the source code contained a hint that inlining this function is desirable (such as
     * the "inline" keyword in C/C++). It is just a hint; it imposes no requirements on the inliner.
     */
    INLINEHINT("inlinehint"),

    /**
     * This attribute disables prologue / epilogue emission for the function. This can have very system-specific
     * consequences.
     */
    NAKED("naked"),

    /**
     * This attribute indicates that calls to the function cannot be duplicated. A call to a noduplicate function may
     * be moved within its parent function, but may not be duplicated within its parent function.
     * A function containing a noduplicate call may still be an inlining candidate, provided that the call is not
     * duplicated by inlining. That implies that the function has internal linkage and only has one call site, so the
     * original call is dead after inlining.
     */
    NODUPLICATE("noduplicate"),

    /**
     * This attributes disables implicit floating point instructions.
     */
    NOIMPLICITFLOAT("noimplicitfloat"),

    /**
     * This attribute indicates that the inliner should never inline this function in any situation. This attribute may
     * not be used together with the alwaysinline attribute.
     */
    NOINLINE("noinline"),

    /**
     * This attribute suppresses lazy symbol binding for the function. This may make calls to the function faster, at
     * the cost of extra program startup time if the function is not called during program startup.
     */
    NOLAZYBIND("nolazybind"),

    /**
     * This attribute indicates that the code generator should not use a red zone, even if the target-specific ABI
     * normally permits it.
     */
    NOREDZONE("noredzone"),

    /**
     * This function attribute indicates that the function never returns normally. This produces undefined behavior at
     * runtime if the function ever does dynamically return.
     */
    NORETURN("noreturn"),

    /**
     * This function attribute indicates that the function never returns with an unwind or exceptional control flow. If
     * the function does unwind, its runtime behavior is undefined.
     */
    NOUNWIND("nounwind"),

    /**
     * This attribute suggests that optimization passes and code generator passes make choices that keep the code size
     * of this function low, and otherwise do optimizations specifically to reduce code size.
     */
    OPTSIZE("optsize"),

    /**
     * This attribute indicates that the function computes its result (or decides to unwind an exception) based
     * strictly on its arguments, without dereferencing any pointer arguments or otherwise accessing any mutable state
     * (e.g. memory, control registers, etc) visible to caller functions. It does not write through any pointer
     * arguments (including byval arguments) and never changes any state visible to callers. This means that it cannot
     * unwind exceptions by calling the C++ exception throwing methods.
     */
    READNONE("readnone"),

    /**
     * This attribute indicates that the function does not write through any pointer arguments (including byval
     * arguments) or otherwise modify any state (e.g. memory, control registers, etc) visible to caller functions. It
     * may dereference pointer arguments and read state that may be set in the caller. A readonly function always
     * returns the same value (or unwinds an exception identically) when called with the same set of arguments and
     * global state. It cannot unwind an exception by calling the C++ exception throwing methods.
     */
    READONLY("readonly"),

    /**
     * This attribute indicates that this function can return twice. The C setjmp is an example of such a function. The
     * compiler disables some optimizations (like tail calls) in the caller of these functions.
     */
    RETURNS_TWICE("returns_twice"),

    /**
     * This attribute indicates that the function should emit a stack smashing protector. It is in the form of a
     * "canary" - a random value placed on the stack before the local variables that's checked upon return from the
     * function to see if it has been overwritten. A heuristic is used to determine if a function needs stack
     * protectors or not.
     * If a function that has an ssp attribute is inlined into a function that doesn't have an ssp attribute, then the
     * resulting function will have an ssp attribute.
     */
    SSP("ssp"),

    /**
     * This attribute indicates that the function should always emit a stack smashing protector. This overrides the ssp
     * function attribute.
     * If a function that has an sspreq attribute is inlined into a function that doesn't have an sspreq attribute or
     * which has an ssp attribute, then the resulting function will have an sspreq attribute.
     */
    SSPREQ("sspreq"),

    /**
     * This attribute indicates that the ABI being targeted requires that an unwind table entry be produce for this
     * function even if we can show that no exceptions passes by it. This is normally the case for the ELF x86-64 abi,
     * but it can be disabled for some compilation units.
     */
    UWTABLE("uwtable");

    /**
     * The name of this function attribute.
     */
    private final String name;

    /**
     * @param n The name of this function attribute.
     */
    private LLVMFunctionAttributeType(final String n) {
        this.name = n;
    }

    /* (non-Javadoc)
     * @see java.lang.Enum#toString()
     */
    @Override
    public String toString() {
        return this.name;
    }

}
