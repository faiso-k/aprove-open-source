package aprove.input.Programs.llvm.parseStructures.exceptions;

import aprove.input.Programs.llvm.internalStructures.module.*;

public class LLVMNotYetSupportedException extends LLVMParseException {

    private static final long serialVersionUID = -8065343725850255513L;

    public LLVMNotYetSupportedException() {
        super("Operation not yet supported.");
    }

    public LLVMNotYetSupportedException(final LLVMBinaryOpType opType) {
        super("Constant expression are not implemented, yet. Usage of operation type: " + opType + ".");
    }

    public LLVMNotYetSupportedException(final LLVMConstExprType opType) {
        super("Constant expression are not implemented, yet. Usage of operation type: " + opType + ".");
    }

}
