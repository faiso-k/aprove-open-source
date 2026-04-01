package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMParseUndefLiteral extends LLVMParseLiteral {

    @Override
    public LLVMLiteral convertToAddressSpace(LLVMType expectedType, Map<String, LLVMType> typeDefs, int pointerSize)
        throws LLVMParseException
    {
        return new LLVMUndefLiteral(expectedType);
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        // undef can be used for any constant except label or void
        if (expectedType.isLabelType() || expectedType.getFirstNonNamedType() instanceof LLVMVoidType) {
            // void or label can not be undefined
            throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
        } else {
            // except void or label types, all literals can be undefined
            return new LLVMUndefLiteral(expectedType);
        }
    }

    @Override
    public String convertToSection() throws LLVMParseException {
        // TODO special value?
        return "undef";
    }

    @Override
    public String toString() {
        return "undef";
    }

}
