package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import immutables.*;

public class LLVMParsePackedStructureType extends LLVMParseType {

    private final List<LLVMParseType> elementTypes;

    public LLVMParsePackedStructureType() {
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
        // we obtain unpacked structures through another type
        return new LLVMStructureType(LLVMPackingType.PACKED, ImmutableCreator.create(elementTypeList));
    }

    @Override
    public String toString() {
        return "packed: " + this.elementTypes.toString();
    }

}
