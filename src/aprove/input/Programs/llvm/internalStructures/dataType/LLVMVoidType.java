package aprove.input.Programs.llvm.internalStructures.dataType;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMVoidType extends LLVMType {

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException {
        throw new LLVMExpectedTypeDoesNotFitException(this, new LLVMZeroInitializer());
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj instanceof LLVMVoidType) {
            return true;
        }
        return false;
    }

    @Override
    public AbstractBoundedInt getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        throw new UnsupportedOperationException("Not yet implemented for this type.");
    }

    @Override
    public IntegerType getIntegerType(boolean unsigned, boolean useBoundedIntegers) {
        throw new UnsupportedOperationException("Not yet implemented for this type");
    }

    @Override
    public int hashCode() {
        return 0;
    }

    @Override
    public int size() {
        return 0;
    }

    @Override
    public String toString() {
        return "BasicVoidType";
    }

}
