package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMParseMetaDataLiteral extends LLVMParseLiteral {

    /**
     * TODO
     */
    public LLVMParseMetaDataLiteral() {
        // TODO Fill with content
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        throw new LLVMNotYetSupportedException();
    }

    @Override
    public String toString() {
        // TODO implement me
        return "Metadata";
    }

}
