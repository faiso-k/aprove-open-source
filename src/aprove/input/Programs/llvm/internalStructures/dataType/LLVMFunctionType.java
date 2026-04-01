package aprove.input.Programs.llvm.internalStructures.dataType;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMFunctionType extends LLVMType {

    /**
     * The types of the function's parameters.
     */
    private final ImmutableList<LLVMType> parameterTypes;

    /**
     * The return type.
     */
    private final LLVMType returnType;

    /**
     * True iff this function has a variable argument list.
     */
    private final boolean varArgument;

    /**
     * @param paramTypes The types of the function's parameters.
     * @param retType The return type.
     * @param varArg True iff this function has a variable argument list.
     */
    public LLVMFunctionType(final List<LLVMType> paramTypes, final LLVMType retType, final boolean varArg) {
        this.parameterTypes = ImmutableCreator.create(paramTypes);
        this.returnType = retType;
        this.varArgument = varArg;
    }

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException {
        throw new LLVMExpectedTypeDoesNotFitException(this, new LLVMZeroInitializer());
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final LLVMFunctionType other = (LLVMFunctionType) obj;
        if (this.parameterTypes == null) {
            if (other.parameterTypes != null) {
                return false;
            }
        } else if (!this.parameterTypes.equals(other.parameterTypes)) {
            return false;
        }
        if (this.returnType == null) {
            if (other.returnType != null) {
                return false;
            }
        } else if (!this.returnType.equals(other.returnType)) {
            return false;
        }
        if (this.varArgument != other.varArgument) {
            return false;
        }
        return true;
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

    /**
     * @return The types of the function's parameters.
     */
    public ImmutableList<LLVMType> getParameterTypes() {
        return this.parameterTypes;
    }

    /**
     * @return The return type.
     */
    public LLVMType getReturnType() {
        return this.returnType;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.parameterTypes == null ? 0 : this.parameterTypes.hashCode());
        result = prime * result + ((this.returnType == null) ? 0 : this.returnType.hashCode());
        result = prime * result + (this.varArgument ? 1231 : 1237);
        return result;
    }

    /**
     * @return True iff this function has a variable argument list.
     */
    public boolean isVarArgument() {
        return this.varArgument;
    }

    @Override
    public int size() {
        throw new UnsupportedOperationException("Don't know the size of a function!");
    }

    @Override
    public String toString() {
        final StringBuilder strBuilder = new StringBuilder("BasicFunctionType ");
        strBuilder.append("varArgs: " + this.varArgument);
        strBuilder.append("returnType: " + this.returnType);
        strBuilder.append("paramTypes: (");
        boolean first = true;
        for (final LLVMType paramType : this.parameterTypes) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(paramType);
        }
        strBuilder.append(")");
        return strBuilder.toString();
    }

}
