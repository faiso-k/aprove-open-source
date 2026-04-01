package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMParseNullLiteral extends LLVMParseLiteral {

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        if (expectedType.isPointerType()) {
            return new LLVMNullLiteral(expectedType);
        } else {
            throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
        }
    }

    @Override
    public String toString() {
        return "null (constant)";
    }

}
