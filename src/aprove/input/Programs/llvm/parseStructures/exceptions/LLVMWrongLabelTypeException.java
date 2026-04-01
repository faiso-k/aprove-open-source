package aprove.input.Programs.llvm.parseStructures.exceptions;

import aprove.input.Programs.llvm.parseStructures.literals.*;

public class LLVMWrongLabelTypeException extends LLVMParseException {

    private static final long serialVersionUID = -7052013329382336665L;

    public LLVMWrongLabelTypeException(LLVMParseLiteral litType) {
        super("Usage of false typed label. Literal is of type " + litType + ", but should be an identifier.");
    }
}
