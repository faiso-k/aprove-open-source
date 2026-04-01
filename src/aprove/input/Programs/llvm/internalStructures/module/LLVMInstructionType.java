package aprove.input.Programs.llvm.internalStructures.module;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public enum LLVMInstructionType {

    /**
     * Alloca instruction.
     */
    ALLOCA,

    /**
     * Binary instruction (add, sub, and, or, etc.).
     */
    BINARY,

    /**
     * Call instruction.
     */
    CALL,

    /**
     * Conditional branch instruction.
     */
    COND_BR,

    /**
     * Conversion instruction (trunc, ptrtoint, etc.).
     */
    CONVERSION,

    /**
     * Extractelement instruction.
     */
    EXTRACTELEMENT,

    /**
     * Extractvalue instruction.
     */
    EXTRACTVALUE,

    /**
     * Comparison instruction for floats.
     */
    FLOAT_CMP,

    /**
     * GEP instruction.
     */
    GETELEMENTPTR,

    /**
     * Indirect branch instruction.
     */
    INDIRECT_BR,

    /**
     * Insertelement instruction.
     */
    INSERTELEMENT,

    /**
     * Insertvalue instruction.
     */
    INSERTVALUE,

    /**
     * Comparison instruction for integers.
     */
    INT_CMP,

    /**
     * Invoke instruction.
     */
    INVOKE,

    /**
     * Load instruction.
     */
    LOAD,

    /**
     * Phi instruction.
     */
    PHI,

    /**
     * Return instruction.
     */
    RET,

    /**
     * Select instruction.
     */
    SELECT,

    /**
     * Shufflevector instruction.
     */
    SHUFFLEVECTOR,

    /**
     * Store instruction.
     */
    STORE,

    /**
     * Switch instruction.
     */
    SWITCH,

    /**
     * Unconditional branch instruction.
     */
    UNCOND_BR,

    /**
     * Unreachable instruction.
     */
    UNREACHABLE,

    /**
     * Unwind instruction.
     */
    UNWIND,

    /**
     * Va_arg instruction.
     */
    VAARG;

    /* (non-Javadoc)
     * @see java.lang.Enum#toString()
     */
    @Override
    public String toString() {
        return this.name().toLowerCase();
    }

}
