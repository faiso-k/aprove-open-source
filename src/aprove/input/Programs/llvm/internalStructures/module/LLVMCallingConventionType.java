package aprove.input.Programs.llvm.internalStructures.module;

/**
 * Calling conventions must match for each caller/callee pair. The default is CCC if nothing else is specified.
 * @author Janine Repke, CryingShadow
 */
public enum LLVMCallingConventionType {

    /**
     * GHC convention
     * This calling convention has been implemented specifically for use by the Glasgow Haskell Compiler (GHC). It
     * passes everything in registers, going to extremes to achieve this by disabling callee save registers. This
     * calling convention should not be used lightly but only for specific situations such as an alternative to the
     * register pinning performance technique often used when implementing functional programming languages. At the
     * moment only X86 supports this convention and it has the following limitations:
     * - On X86-32 only supports up to 4 bit type parameters. No floating point types are supported.
     * - On X86-64 only supports up to 10 bit type parameters and 6 floating point parameters.
     * This calling convention supports tail call optimization but requires both the caller and callee are using it.
     */
    CC_10("cc 10"),

    /**
     * The HiPE calling convention
     * This calling convention has been implemented specifically for use by the High-Performance Erlang (HiPE)
     * compiler, the native code compiler of the Ericsson’s Open Source Erlang/OTP system. It uses more registers for
     * argument passing than the ordinary C calling convention and defines no callee-saved registers. The calling
     * convention properly supports tail call optimization but requires that both the caller and the callee use it. It
     * uses a register pinning mechanism, similar to GHC’s convention, for keeping frequently accessed runtime
     * components pinned to specific hardware registers. At the moment only X86 supports this convention (both 32 and
     * 64 bit).
     */
    CC_11("cc 11"),

    /**
     * Numbered convention
     * Any calling convention may be specified by number, allowing target-specific calling conventions to be used.
     * Target specific calling conventions start at 64.
     * Its number is specified outside this enum.
     */
    CC_N("cc "),

    /**
     * The C calling convention
     * This calling convention (the default if no other calling convention is specified) matches the target C calling
     * conventions. This calling convention supports varargs function calls and tolerates some mismatch in the declared
     * prototype and implemented declaration of the function (as does normal C).
     */
    CCC("ccc"),

    /**
     * The cold calling convention
     * This calling convention attempts to make code in the caller as efficient as possible under the assumption that
     * the call is not commonly executed. As such, these calls often preserve all registers so that the call does not
     * break any live ranges in the caller side. This calling convention does not support varargs and requires the
     * prototype of all callees to exactly match the prototype of the function definition.
     */
    COLDCC("coldcc"),

    /**
     * The fast calling convention
     * This calling convention attempts to make calls as fast as possible (e.g. by passing things in registers). This
     * calling convention allows the target to use whatever tricks it wants to produce fast code for the target,
     * without having to conform to an externally specified ABI (Application Binary Interface). Tail calls can only be
     * optimized when this, the GHC or the HiPE convention is used. This calling convention does not support varargs
     * and requires the prototype of all callees to exactly match the prototype of the function definition.
     */
    FASTCC("fastcc");

    /**
     * The name of the calling convention.
     */
    private final String name;

    /**
     * @param n The name of the calling convention.
     */
    private LLVMCallingConventionType(final String n) {
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
