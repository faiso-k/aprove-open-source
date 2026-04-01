package aprove.input.Programs.llvm.parseStructures.exceptions;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;

public class LLVMExpectedTypeDoesNotFitException extends LLVMParseException {

    private static final long serialVersionUID = -262888446186845185L;

    public LLVMExpectedTypeDoesNotFitException(LLVMType expectedType, LLVMParseLiteral litType) {
        super("Expected type is:" + expectedType.toString() + " But the literal has value " + litType.toString() + ".");
    }

}
