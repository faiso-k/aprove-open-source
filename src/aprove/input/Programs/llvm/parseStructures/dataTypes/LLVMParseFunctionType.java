package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

public class LLVMParseFunctionType extends LLVMParseType {

    private final List<LLVMParseType> parameterTypes;

    private LLVMParseType returnType;

    // true if function has a variable argument list
    private boolean varArgument;

    public LLVMParseFunctionType() {
        this.returnType = null;
        this.parameterTypes = new ArrayList<LLVMParseType>();
        this.varArgument = false;
    }

    public void addParameter(LLVMParseType parameter) {
        this.parameterTypes.add(parameter);
    }

    @Override
    public boolean checkIfTypeIsPrimitiveType(LLVMParseModule module) {
        return false;
    }

    @Override
    public boolean checkifTypeIsVectorElementType(LLVMParseModule module) {
        return false;
    }

    @Override
    public LLVMType convertToBasicType(Map<String, LLVMType> typeDefs, int pointerSize) throws LLVMParseException {
        List<LLVMType> paramTypes = new ArrayList<LLVMType>();
        for (LLVMParseType parameterType : this.parameterTypes) {
            paramTypes.add(parameterType.convertToBasicType(typeDefs, pointerSize));
        }
        return
            new LLVMFunctionType(
                paramTypes,
                this.returnType.convertToBasicType(typeDefs, pointerSize),
                this.varArgument
            );
    }

    public LLVMParseType getReturnType() {
        return this.returnType;
    }

    public boolean isVarArgument() {
        return this.varArgument;
    }

    public void setReturnType(LLVMParseType retType) {
        this.returnType = retType;
    }

    public void setVarArgument(boolean varArg) {
        this.varArgument = varArg;
    }

    @Override
    public String toString() {
        return this.returnType.toString() + " " + this.parameterTypes.toString() + (this.varArgument ? " (...)" : "");
    }

}
