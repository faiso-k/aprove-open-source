package aprove.input.Programs.llvm.internalStructures.module;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public enum LLVMDataType {

    /**
     * Array type.
     */
    ARRAY,

    /**
     * Double type.
     */
    DOUBLE,

    /**
     * Float type.
     */
    FLOAT,

    /**
     * Float type with 128 bits (112-bit mantissa).
     */
    FP128,

    /**
     * Function type.
     */
    FUNCTION,

    /**
     * Integer type.
     */
    INT,

    /**
     * Label type.
     */
    LABEL,

    /**
     * Metadata type.
     */
    METADATA,

    /**
     * Named type (according to type definitions in LLVMModule).
     */
    NAMED,

    /**
     * Opaque type.
     */
    OPAQUE,

    /**
     * Pointer type.
     */
    POINTER,

    /**
     * Float type with 128 bits (two 64-bits).
     */
    PPC_FP128,

    /**
     * String type.
     */
    STRING,

    /**
     * Structure type.
     */
    STRUCTURE,

    /**
     * Variable argument list type.
     */
    VALIST,

    /**
     * Vector type.
     */
    VECTOR,

    /**
     * Void type.
     */
    VOID,

    /**
     * Float type with 80 bits.
     */
    X86_FP80;

}
