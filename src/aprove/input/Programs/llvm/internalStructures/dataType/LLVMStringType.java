package aprove.input.Programs.llvm.internalStructures.dataType;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * @author CryingShadow
 */
public class LLVMStringType extends LLVMType {

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException {
        throw new UnsupportedOperationException("Initialization of Strings is not yet supported!");
    }

    @Override
    public boolean equals(Object other){
        throw new UnsupportedOperationException("Equality calculation of Strings is not yet supported!");
    }

    @Override
    public AbstractBoundedInt getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        throw new UnsupportedOperationException("Initialization of Strings is not yet supported!");
    }

    @Override
    public int hashCode(){
        throw new UnsupportedOperationException("Hash calculation of Strings is not yet supported!");
    }

    @Override
    public IntegerType getIntegerType(boolean unsigned, boolean useBoundedIntegers) {
        throw new UnsupportedOperationException("Not yet implemented for this type");
    }

    @Override
    public int size() {
        throw new UnsupportedOperationException("Size calculation of Strings is not yet supported!");
    }

}
