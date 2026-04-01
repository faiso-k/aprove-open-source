package aprove.input.Programs.llvm.internalStructures.module;

/**
 * @author Janine Repke, CryingShadow
 * TODO documentation
 */
public enum LLVMLinkageType {

    /**
     *
     */
    APPENDING,

    /**
     *
     */
    AVAILABLE_EXTERNALLY,

    /**
     *
     */
    COMMON,

    /**
     *
     */
    DLLEXPORT,

    /**
     * WINDOWS SPECIFIC LINKAGE TYPE
     */
    DLLIMPORT,

    /**
     *
     */
    EXTERN_WEAK,

    /**
     *
     */
    EXTERNAL,

    /**
     * default type
     */
    EXTERNALLY_VISIBLE,

    /**
     *
     */
    INTERNAL,

    /**
     *
     */
    LINKER_PRIVATE,

    /**
     *
     */
    LINKER_PRIVATE_WEAK,

    /**
     *
     */
    LINKER_PRIVATE_WEAK_DEF_AUTO,

    /**
     *
     */
    LINKONCE,

    /**
     *
     */
    LINKONCE_ODR,

    /**
     *
     */
    PRIVATE,

    /**
     *
     */
    WEAK,

    /**
     *
     */
    WEAK_ODR;

    /**
     * @return The default type.
     */
    public static LLVMLinkageType getDefaultType() {
        return EXTERNALLY_VISIBLE;
    }
}
