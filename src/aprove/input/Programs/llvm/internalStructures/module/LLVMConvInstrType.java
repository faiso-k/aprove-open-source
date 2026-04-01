package aprove.input.Programs.llvm.internalStructures.module;

/**
 * @author Janine Repke, CryingShadow
 * Types of conversion instructions.
 */
public enum LLVMConvInstrType {

    /**
     * Bitcast.
     */
    BITCAST,

    /**
     * TODO
     */
    FPEXT,

    /**
     * Floating point to signed integer.
     */
    FPTOSI,

    /**
     * Floating point to unsigned integer.
     */
    FPTOUI,

    /**
     * TODO
     */
    FPTRUNC,

    /**
     * TODO
     */
    INTTOPTR,

    /**
     * TODO
     */
    PTRTOINT,

    /**
     * TODO
     */
    SEXT,

    /**
     * TODO
     */
    SITOFP,

    /**
     * TODO
     */
    TRUNC,

    /**
     * TODO
     */
    UITOFP,

    /**
     * TODO
     */
    ZEXT;

    /* (non-Javadoc)
     * @see java.lang.Enum#toString()
     */
    @Override
    public String toString() {
        return this.name().toLowerCase();
    }

}
