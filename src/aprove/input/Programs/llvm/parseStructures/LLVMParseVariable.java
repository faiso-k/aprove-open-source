package aprove.input.Programs.llvm.parseStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.dataTypes.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;

public class LLVMParseVariable {

    private LLVMParseLiteral addrSpace = null;
    private LLVMParseLiteral alignment = null;
    private boolean constant = false; // a variable is either constant or global, constant means that the content of the variable will never be modified
    private LLVMParseLiteral initValue = null; // the init value is optional

    // TODO Another type better? Maybe object?
    // TODO this String is not used yet - what is it for?
    private String initValueString = null;

    private LLVMLinkageType linkageType = null;
    private final String name; // variable name without leading $- or @-sign
    private final LLVMParseType parseType;
    private LLVMParseLiteral section = null;

    private boolean threadLocal = false; // if true, the variable will not be shared by threads
    private String typeString; // String representation of the type, online used for debugging

    public LLVMParseVariable(final String name, final LLVMParseType type) {
        this.name = name;
        this.parseType = type;
    }

    public LLVMGlobalVariable convertToGlobalVariable(final Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        final LLVMType expectedType = this.parseType.convertToBasicType(typeDefs, pointerSize);
        return
            new LLVMGlobalVariable(
                this.name,
                expectedType,
                this.addrSpace == null ?
                    null :
                        this.addrSpace.convertToAddressSpace(expectedType, typeDefs, pointerSize),
                this.alignment == null ?
                    null :
                        this.alignment.convertToAlignment(pointerSize),
                this.threadLocal,
                this.constant,
                this.initValue == null ?
                    null :
                        this.initValue.convertToBasicLiteral(expectedType, false, typeDefs, pointerSize),
                this.linkageType,
                this.section == null ?
                    null :
                        this.section.convertToSection()
            );
    }

    public LLVMParseLiteral getAddrSpace() {
        return this.addrSpace;
    }

    public LLVMParseLiteral getAlignment() {
        return this.alignment;
    }

    public LLVMParseLiteral getInitValue() {
        return this.initValue;
    }

    public String getInitValueString() {
        return this.initValueString;
    }

    public LLVMLinkageType getLinkageType() {
        return this.linkageType;
    }

    public LLVMParseLiteral getSection() {
        return this.section;
    }

    public String getTypeString() {
        return this.typeString;
    }

    public boolean isConstant() {
        return this.constant;
    }

    public boolean isThreadLocal() {
        return this.threadLocal;
    }

    public void setAddrSpace(final LLVMParseLiteral addrSpace) {
        this.addrSpace = addrSpace;
    }

    public void setAlignment(final LLVMParseLiteral alignment) {
        this.alignment = alignment;
    }

    public void setConstant(final boolean constant) {
        this.constant = constant;
    }

    public void setInitValue(final LLVMParseLiteral initValue) {
        this.initValue = initValue;
    }

    public void setInitValueString(final String initValueString) {
        this.initValueString = initValueString;
    }

    public void setLinkageType(final LLVMLinkageType linkType) {
        this.linkageType = linkType;
        if (linkType == null) {
            // set to default value
            this.linkageType = LLVMLinkageType.getDefaultType();
        }
    }

    public void setSection(final LLVMParseLiteral section) {
        this.section = section;
    }

    public void setThreadLocal(final boolean threadLocal) {
        this.threadLocal = threadLocal;
    }

    public void setTypeString(final String typeString) {
        this.typeString = typeString;
    }

    /*
     * Only used for debug output.
     */
    @Override
    public String toString() {
        final StringBuilder strBuilder = new StringBuilder("\"" + this.name + "\" \"" + this.typeString + "\" ");

        if (this.initValueString != null) {
            strBuilder.append(" \"" + this.initValueString + "\" ");
        }

        if (this.linkageType != null) {
            strBuilder.append(" linkageType:\"" + this.linkageType + "\" ");
        }

        if (this.constant) {
            strBuilder.append(" \"constant\" ");
        } else {
            strBuilder.append(" \"global\" ");
        }

        /*
         * if(addrSpace >= 0) { str += "addrSpace: \"" + addrSpace + "\""; }
         */

        return strBuilder.toString();
    }

}
