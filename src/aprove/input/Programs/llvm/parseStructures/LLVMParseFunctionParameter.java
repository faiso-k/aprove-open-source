package aprove.input.Programs.llvm.parseStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.dataTypes.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import immutables.*;

/**
 * Represents function parameters and also return types. A function parameter
 * has a type, optional parameter attributes and may have a name (for function
 * definitions).
 *
 */
public class LLVMParseFunctionParameter {

    private final HashSet<LLVMParameterAttribute> attributes = new HashSet<LLVMParameterAttribute>();
    private String name = null; // optional, parameters in function definitions have a name, in function declarations not
    private LLVMParseType type;

    public LLVMParseFunctionParameter() {
        // constructor without initial values
    }

    public LLVMParseFunctionParameter(LLVMParseType type) {
        this.type = type;
    }

    public LLVMParseFunctionParameter(String name, LLVMParseType type) {
        this(type);
        this.name = name;
    }

    public void addAttribute(LLVMParameterAttribute attribute) {
        this.attributes.add(attribute);
    }

    public LLVMFnParameter convertToFnParameter(Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        return
            new LLVMFnParameter(
                this.name,
                this.type.convertToBasicType(typeDefs, pointerSize),
                ImmutableCreator.create(this.attributes)
            );
    }

    public HashSet<LLVMParameterAttribute> getAttributes() {
        return this.attributes;
    }

    public String getName() {
        return this.name;
    }

    public LLVMParseType getType() {
        return this.type;
    }

    public void setName(String name) {
        this.name = name;
    }

    public void setType(LLVMParseType type) {
        this.type = type;
    }

    @Override
    public String toString() {
        String str = "";
        if (this.name != null) {
            str = this.name;
        }
        // str += type + " ";

        for (LLVMParameterAttribute attr : this.attributes) {
            str += attr.toString() + " ";
        }
        return str;
    }

}
