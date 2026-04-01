package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMParseVoidLiteral extends LLVMParseLiteral {

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        // this method should never be used for void
        throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
    }

    @Override
    public String toString() {
        return "void";
    }

}
