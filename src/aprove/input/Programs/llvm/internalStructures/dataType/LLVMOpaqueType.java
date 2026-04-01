package aprove.input.Programs.llvm.internalStructures.dataType;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMOpaqueType extends LLVMType {

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException {
        throw new LLVMNotYetSupportedException();
    }

    @Override
    public boolean equals(final Object obj) {
        return obj instanceof LLVMOpaqueType;
    }

    @Override
    public AbstractBoundedInt getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        // TODO return (-inf,+inf) instead?
        throw new UnsupportedOperationException("Cannot determine a value for an opaque type.");
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
        throw new UnsupportedOperationException("Opaque types are not yet supported!");
    }

    @Override
    public String toString() {
        final StringBuilder strBuilder = new StringBuilder("BasicOpaqueType");
        return strBuilder.toString();
    }

}
