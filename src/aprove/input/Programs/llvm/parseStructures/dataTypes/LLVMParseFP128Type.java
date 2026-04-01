package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * Floating point type with 128-bit. (112-bit mantissa)
 */
public class LLVMParseFP128Type extends LLVMParseType {

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
        throw new LLVMTypeNotSupportedException(this);
        //return new BasicFP128Type();
    }

    @Override
    public String toString() {
        return "FP128";
    }

}
