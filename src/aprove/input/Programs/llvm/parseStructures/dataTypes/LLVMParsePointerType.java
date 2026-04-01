package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;

public class LLVMParsePointerType extends LLVMParseType {

    private LLVMParseLiteral addressSpace; // optional address space

    private LLVMParseType targetType;

    public LLVMParsePointerType(LLVMParseType targetType) {
        this.targetType = targetType;
    }

    @Override
    public boolean checkIfTypeIsPrimitiveType(LLVMParseModule module) {
        // a pointer type is a derived type and so no primitive type
        return false;
    }

    @Override
    public boolean checkifTypeIsVectorElementType(LLVMParseModule module) {
        return false;
    }

    @Override
    public LLVMType convertToBasicType(Map<String, LLVMType> typeDefs, int pointerSize) throws LLVMParseException {
        // any element type is allowed
        LLVMType type = this.targetType.convertToBasicType(typeDefs, pointerSize);
        LLVMLiteral bAddressSpace = null;
        if (this.addressSpace != null) {
            bAddressSpace = this.addressSpace.convertToAddressSpace(type, typeDefs, pointerSize);
        }
        return new LLVMPointerType(type, pointerSize, bAddressSpace);
    }

    public LLVMParseLiteral getAddressSpace() {
        return this.addressSpace;
    }

    public LLVMParseType getTargetType() {
        return this.targetType;
    }

    public void setAddressSpace(LLVMParseLiteral addressSpace) {
        this.addressSpace = addressSpace;
    }

    public void setTargetType(LLVMParseType targetType) {
        this.targetType = targetType;
    }

    @Override
    public String toString() {
        return this.targetType.toString() + "*";
    }

}
