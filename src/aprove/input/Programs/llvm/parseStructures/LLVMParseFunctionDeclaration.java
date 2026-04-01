package aprove.input.Programs.llvm.parseStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;
import immutables.*;

public class LLVMParseFunctionDeclaration {
    protected LLVMParseLiteral alignment = null;
    protected HashSet<LLVMFunctionAttribute> attributes = new HashSet<LLVMFunctionAttribute>();
    protected LLVMCallingConvention callConv = new LLVMCallingConvention(LLVMCallingConventionType.CCC);
    protected String garColl = null; // optional garbage collector name
    protected LLVMLinkageType linkageType = null; // what is the default linkage type?
    protected String name; // name of the function
    protected ArrayList<LLVMParseFunctionParameter> parameters = new ArrayList<LLVMParseFunctionParameter>();
    protected LLVMParseFunctionParameter returnParam = null;
    protected boolean variableLength = false; // specifies if this function has an variable-length argument list
    protected LLVMVisibilityType visType = LLVMVisibilityType.DEFAULT;

    public void addAttribute(LLVMFunctionAttribute attribute) {
        this.attributes.add(attribute);
    }

    public void addParameter(LLVMParseFunctionParameter param) {
        this.parameters.add(param);
    }

    public LLVMFnDeclaration convertToFnDeclaration(Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        return
            new LLVMFnDeclaration(
                this.alignment == null ? null : this.alignment.convertToAlignment(pointerSize),
                this.attributes == null ? null : ImmutableCreator.create(this.attributes),
                this.callConv,
                this.garColl,
                this.linkageType,
                this.name,
                this.convertToFnParameters(typeDefs, pointerSize),
                this.returnParam.convertToFnParameter(typeDefs, pointerSize),
                this.variableLength,
                this.visType
            );
    }

    public ImmutableList<LLVMFnParameter> convertToFnParameters(Map<String, LLVMType> typeDefs, int pointerSize)
        throws LLVMParseException
    {
        // convert all function parameters
        final List<LLVMFnParameter> params = new ArrayList<LLVMFnParameter>();
        for (LLVMParseFunctionParameter parameter : this.parameters) {
            params.add(parameter.convertToFnParameter(typeDefs, pointerSize));
        }
        return ImmutableCreator.create(params);
    }

    public LLVMParseLiteral getAlignment() {
        return this.alignment;
    }

    public HashSet<LLVMFunctionAttribute> getAttributes() {
        return this.attributes;
    }

    public LLVMCallingConvention getCallConv() {
        return this.callConv;
    }

    public String getGarColl() {
        return this.garColl;
    }

    public LLVMLinkageType getLinkageType() {
        return this.linkageType;
    }

    public String getName() {
        return this.name;
    }

    public ArrayList<LLVMParseFunctionParameter> getParameters() {
        return this.parameters;
    }

    public LLVMParseFunctionParameter getReturnType() {
        return this.returnParam;
    }

    public LLVMVisibilityType getVisType() {
        return this.visType;
    }

    public boolean isVariableLength() {
        return this.variableLength;
    }

    public void setAlignment(LLVMParseLiteral alignment) {
        this.alignment = alignment;
    }

    public void setCallConv(LLVMCallingConvention callConv) {
        if (callConv == null) {
            this.callConv = new LLVMCallingConvention(LLVMCallingConventionType.CCC);
        } else {
            this.callConv = callConv;
        }
    }

    public void setGarColl(String garColl) {
        this.garColl = garColl;
    }

    public void setLinkageType(LLVMLinkageType linkageType) {
        this.linkageType = linkageType;
        if (linkageType == null) {
            this.linkageType = LLVMLinkageType.getDefaultType();
        }
    }

    public void setName(String name) {
        this.name = name;
    }

    public void setReturnType(LLVMParseFunctionParameter returnType) {
        this.returnParam = returnType;
    }

    public void setVariableLength(boolean variableLengthArgList) {
        this.variableLength = variableLengthArgList;
    }

    public void setVisType(LLVMVisibilityType visType) {
        if (visType == null) {
            this.visType = LLVMVisibilityType.DEFAULT;
        } else {
            this.visType = visType;
        }
    }

    @Override
    public String toString() {
        return this.returnParam.toString() + " " + this.name + this.parameters.toString();
    }

}
