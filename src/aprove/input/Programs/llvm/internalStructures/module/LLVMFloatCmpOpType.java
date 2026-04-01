package aprove.input.Programs.llvm.internalStructures.module;

/**
 * @author Janine Repke, CryingShadow
 * special operation types for floating compare operations
 * TODO documentation
 */
public enum LLVMFloatCmpOpType {

    /**
     *
     */
    FALSE,

    /**
     *
     */
    OEQ,

    /**
     *
     */
    OGE,

    /**
     *
     */
    OGT,

    /**
     *
     */
    OLE,

    /**
     *
     */
    OLT,

    /**
     *
     */
    ONE,

    /**
     *
     */
    ORD,

    /**
     *
     */
    TRUE,

    /**
     *
     */
    UEQ,

    /**
     *
     */
    UGE,

    /**
     *
     */
    UGT,

    /**
     *
     */
    ULE,

    /**
     *
     */
    ULT,

    /**
     *
     */
    UNE,

    /**
     *
     */
    UNO;

    /* (non-Javadoc)
     * @see java.lang.Enum#toString()
     */
    @Override
    public String toString() {
        return this.name().toLowerCase();
    }

}
