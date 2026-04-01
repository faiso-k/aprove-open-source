package aprove.input.Programs.llvm.parseStructures.exceptions;

import aprove.input.Programs.llvm.parseStructures.dataTypes.*;

public class LLVMTypeNotSupportedException extends LLVMParseException {

    private static final long serialVersionUID = -4139728216093199088L;

    public LLVMTypeNotSupportedException(LLVMParseType type) {
        super("Type " + type + " is not supported yet.");
    }

}
