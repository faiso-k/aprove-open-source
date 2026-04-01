package aprove.input.Programs.llvm.internalStructures.dataType;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * Floating point type with 32-bit
 * @author Janine Repke, cryingshadow
 * @version $Id$
 */
public class LLVMFloatType extends LLVMType {

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) {
        return new LLVMFloatLiteral(0);
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj instanceof LLVMFloatType) {
            return true;
        }
        return false;
    }

    @Override
    public AbstractFloat getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        return AbstractFloat.create();
    }

    @Override
    public IntegerType getIntegerType(boolean unsigned, boolean useBoundedIntegers) {
        return IntegerType.I32;
    }

    @Override
    public int hashCode() {
        return 0;
    }

    @Override
    public int size() {
        return 32;
    }

    @Override
    public String toString() {
        return "BasicFloatType";
    }

}
