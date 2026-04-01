package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import immutables.*;

public class LLVMParseStructureType extends LLVMParseType {

    private final List<LLVMParseType> elementTypes;

    public LLVMParseStructureType() {
        this.elementTypes = new ArrayList<LLVMParseType>();
    }

    public void addElementType(LLVMParseType elementType) {
        this.elementTypes.add(elementType);
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
        List<LLVMType> elementTypeList = new ArrayList<LLVMType>();
        for (LLVMParseType elementType : this.elementTypes) {
            elementTypeList.add(elementType.convertToBasicType(typeDefs, pointerSize));
        }
        // we obtain packed structures through another type
        return new LLVMStructureType(LLVMPackingType.NORMAL, ImmutableCreator.create(elementTypeList));
    }

    @Override
    public String toString() {
        return "{" + this.elementTypes.toString() + "}";
    }

}
