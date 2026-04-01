package aprove.input.Programs.llvm.internalStructures.module;

/**
 * @author Janine Repke, CryingShadow
 * Types of constant expressions.
 */
public enum LLVMConstExprType {

    /**
     * Binary expression.
     */
    BINARY,

    /**
     * Conversion expression.
     */
    CONVERSION,

    /**
     * Extractelement expression.
     */
    EXTRACT_ELEMENT,

    /**
     * Extractvalue expression.
     */
    EXTRACT_VALUE,

    /**
     * Comparison expression with floats.
     */
    FLOAT_CMP,

    /**
     * GEP expression.
     */
    GET_ELEMENT_PTR,

    /**
     * Insertelement expression.
     */
    INSERT_ELEMENT,

    /**
     * Insertvalue expression.
     */
    INSERT_VALUE,

    /**
     * Comparison expression with integers.
     */
    INT_CMP,

    /**
     * Select expression.
     */
    SELECT,

    /**
     * Shufflevector expression.
     */
    SHUFFLE_VECTOR,

    /**
     * Va_arg expression.
     */
    VAARG;

}
