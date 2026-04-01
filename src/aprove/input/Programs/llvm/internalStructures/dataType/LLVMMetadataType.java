package aprove.input.Programs.llvm.internalStructures.dataType;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMMetadataType extends LLVMType {

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException {
        throw new LLVMNotYetSupportedException();
    }

    @Override
    public boolean equals(final Object obj) {
        // TODO
        if (obj instanceof LLVMMetadataType) {
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
        // TODO
        return 0;
    }

    @Override
    public int size() {
        throw new UnsupportedOperationException("Don't know the size of metadata!");
    }

    @Override
    public String toString() {
        final String str = new String("BasicMetadataType");
        return str;
    }

}
