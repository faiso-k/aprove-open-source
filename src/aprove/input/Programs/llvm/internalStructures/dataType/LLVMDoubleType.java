package aprove.input.Programs.llvm.internalStructures.dataType;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * Floating point type with 64-bit. TODO use layout
 * @author Janine Repke, cryingshadow
 * @version $Id$
 */
public class LLVMDoubleType extends LLVMType {

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) {
        return new LLVMDoubleLiteral(0);
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj instanceof LLVMDoubleType && obj != null) {
            return true;
        }
        return false;
    }

    @Override
    public AbstractNumber getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        // TODO adapt for double
        return AbstractFloat.create();
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
        return 64;
        //TODO use layout
    }

    @Override
    public String toString() {
        final String str = "BasicDoubleType";
        return str;
    }

}
