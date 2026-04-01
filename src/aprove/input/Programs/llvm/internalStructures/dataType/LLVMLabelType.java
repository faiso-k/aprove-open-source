package aprove.input.Programs.llvm.internalStructures.dataType;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMLabelType extends LLVMType {

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException {
        throw new LLVMExpectedTypeDoesNotFitException(this, new LLVMZeroInitializer());
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj instanceof LLVMLabelType) {
            return true;
        }
        return false;
    }

    @Override
    public AbstractBoundedInt getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        // TODO Auto-generated method stub
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
    public boolean isLabelType() {
        return true;
    }

    @Override
    public int size() {
        throw new UnsupportedOperationException("Don't know the size of a label!");
    }

    @Override
    public String toString() {
        final String str = "BasicLabelType";
        return str;
    }

}
