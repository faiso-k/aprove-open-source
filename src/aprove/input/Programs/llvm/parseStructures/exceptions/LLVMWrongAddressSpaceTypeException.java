package aprove.input.Programs.llvm.parseStructures.exceptions;

import aprove.input.Programs.llvm.parseStructures.literals.*;

public class LLVMWrongAddressSpaceTypeException extends LLVMParseException {

    private static final long serialVersionUID = -2025685573846483890L;

    public LLVMWrongAddressSpaceTypeException(LLVMParseLiteral litType) {
        super("Usage of false typed address space. Literal is of type " + litType + ", but should be an integer.");
    }

}
