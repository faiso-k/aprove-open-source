package aprove.input.Programs.llvm.parseStructures.exceptions;

import aprove.input.Programs.llvm.internalStructures.dataType.*;

public class LLVMWrongHexFormatException extends LLVMParseException {

    private static final long serialVersionUID = -3628429362483972413L;

    public LLVMWrongHexFormatException(LLVMType expectedType, String hexString) {
        super("The expected Type does not fit with the given hex literal. Expected type is: "
            + expectedType.toString()
            + " The hex string is: "
            + hexString);
    }

}
