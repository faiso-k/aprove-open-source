package aprove.input.Programs.llvm.parseStructures.exceptions;

import aprove.input.Programs.llvm.parseStructures.literals.*;

public class LLVMWrongSectionTypeException extends LLVMParseException {

    private static final long serialVersionUID = 7898904358705682144L;

    public LLVMWrongSectionTypeException(LLVMParseLiteral litType) {
        super("Section name has a wrong type. Literal is of type " + litType + ", but should specify a string.");
    }

}
