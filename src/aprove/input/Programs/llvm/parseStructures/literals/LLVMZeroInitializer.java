package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * @author Janine Repke, CryingShadow
 * Literal with some kind of default value.
 */
public class LLVMZeroInitializer extends LLVMParseLiteral {

    @Override
    public LLVMLiteral convertToAddressSpace(LLVMType expectedType, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        return new LLVMRegularIntLiteral(32, 0, true);
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        return expectedType.convertToZeroInitializedLiteral(unsigned);
    }

}
