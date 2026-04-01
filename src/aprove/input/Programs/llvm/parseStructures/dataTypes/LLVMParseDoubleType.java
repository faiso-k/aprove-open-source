package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * Floating point type with 64-bit.
 */
public class LLVMParseDoubleType extends LLVMParseType {

    @Override
    public boolean checkIfTypeIsPrimitiveType(LLVMParseModule module) {
        return true;
    }

    @Override
    public boolean checkifTypeIsVectorElementType(LLVMParseModule module) {
        return true;
    }

    @Override
    public LLVMType convertToBasicType(Map<String, LLVMType> typeDefs, int pointerSize) throws LLVMParseException {
        return new LLVMDoubleType();
    }

    @Override
    public String toString() {
        return "double";
    }

}
