package aprove.input.Programs.llvm.parseStructures.exceptions;

import aprove.input.Programs.llvm.parseStructures.literals.*;

public class LLVMWrongVariableNameTypeException extends LLVMParseException {

    private static final long serialVersionUID = -2853702300176949926L;

    public LLVMWrongVariableNameTypeException(LLVMParseLiteral litType) {
        super("Usage of false typed varname. Literal is of type " + litType + ", but should be a variable.");
    }

}
