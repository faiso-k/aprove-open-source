package aprove.input.Programs.llvm.internalStructures.module;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import immutables.*;

/**
 * This class contains an alias definition of an LLVM program. Aliases act as
 * "second name" for the aliasee value (which can be either function, global
 * variable, another alias or bitcast of global value).
 *
 * @author Janine Repke, cryingshadow
 */
public class LLVMAliasDefinition implements Immutable {

    /**
     * The aliased name.
     */
    private final String aliasedName;

    /**
     * The aliased type.
     */
    private final LLVMType aliasedType;

    /**
     * The alias.
     */
    private final String aliasName;

    /**
     * TODO documentation
     * optional
     */
    private final LLVMAliasLinkageType linkageType;

    /**
     * TODO docu guess: The visibility type.
     * optional
     */
    private final LLVMVisibilityType visType;

    /**
     * @param alias The alias.
     * @param type The aliased type.
     * @param aliased The aliased name.
     * @param linkType TODO documentation
     * @param vType TODO docu guess: The visibility type.
     */
    public LLVMAliasDefinition(
        String alias,
        LLVMType type,
        String aliased,
        LLVMAliasLinkageType linkType,
        LLVMVisibilityType vType)
    {
        this.aliasName = alias;
        this.aliasedType = type;
        this.aliasedName = aliased;
        this.linkageType = linkType;
        this.visType = vType;
    }

    /**
     * @return The alias.
     */
    public String getAlias() {
        return this.aliasName;
    }

    /**
     * @return The aliased name.
     */
    public String getAliasedName() {
        return this.aliasedName;
    }

    /**
     * @return The aliased type.
     */
    public LLVMType getAliasedType() {
        return this.aliasedType;
    }

    /**
     * @return TODO documentation
     */
    public LLVMAliasLinkageType getLinkageType() {
        return this.linkageType;
    }

    /**
     * @return TODO docu guess: The visibility type.
     */
    public LLVMVisibilityType getVisType() {
        return this.visType;
    }

}
