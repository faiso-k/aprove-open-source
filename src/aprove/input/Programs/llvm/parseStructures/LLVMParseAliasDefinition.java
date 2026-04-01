package aprove.input.Programs.llvm.parseStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.dataTypes.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

public class LLVMParseAliasDefinition {

    private String aliasedName;
    private LLVMParseType aliasedType;
    private String aliasName;
    private LLVMAliasLinkageType linkageType; // optional
    private LLVMVisibilityType visType; // optional

    public LLVMAliasDefinition convertToAliasDefinition(final Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        return
            new LLVMAliasDefinition(
                this.aliasName,
                this.aliasedType.convertToBasicType(typeDefs, pointerSize),
                this.aliasedName,
                this.linkageType,
                this.visType
            );
    }

    public String getAliasedName() {
        return this.aliasedName;
    }

    public LLVMParseType getAliasedType() {
        return this.aliasedType;
    }

    public String getAliasName() {
        return this.aliasName;
    }

    public LLVMAliasLinkageType getLinkageType() {
        return this.linkageType;
    }

    public LLVMVisibilityType getVisType() {
        return this.visType;
    }

    public void setAliasedName(final String aliasedName) {
        this.aliasedName = aliasedName;
    }

    public void setAliasedType(final LLVMParseType aliasedType) {
        this.aliasedType = aliasedType;
    }

    public void setAliasName(final String aliasName) {
        this.aliasName = aliasName;
    }

    public void setLinkageType(final LLVMAliasLinkageType linkageType) {
        this.linkageType = linkageType;
    }

    public void setVisType(final LLVMVisibilityType visType) {
        this.visType = visType;
    }

    @Override
    public String toString() {
        return this.aliasName + ": (" + this.aliasedName + ", " + this.aliasedType + ")";
    }

}
