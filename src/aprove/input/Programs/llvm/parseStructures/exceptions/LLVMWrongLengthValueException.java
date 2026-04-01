package aprove.input.Programs.llvm.parseStructures.exceptions;

import aprove.input.Programs.llvm.internalStructures.dataType.*;

public class LLVMWrongLengthValueException extends LLVMParseException {

    private static final long serialVersionUID = 8935272299332146315L;

    public LLVMWrongLengthValueException(LLVMType litType) {
        super("Usage of false typed length. Literal is of type " + litType.toString() + ", but should be an integer.");
    }

}
