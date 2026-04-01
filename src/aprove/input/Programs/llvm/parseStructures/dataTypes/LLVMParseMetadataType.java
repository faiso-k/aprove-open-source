package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

public class LLVMParseMetadataType extends LLVMParseType {

    @Override
    public boolean checkIfTypeIsPrimitiveType(LLVMParseModule module) {
        return true;
    }

    @Override
    public boolean checkifTypeIsVectorElementType(LLVMParseModule module) {
        return false;
    }

    @Override
    public LLVMType convertToBasicType(Map<String, LLVMType> typeDefs, int pointerSize) throws LLVMParseException {
        return new LLVMMetadataType();
    }

    @Override
    public String toString() {
        return "Metadata";
    }

}
