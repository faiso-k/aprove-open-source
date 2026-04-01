package aprove.input.Programs.llvm.internalStructures.dataType;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMVectorType extends LLVMType {

    /**
     * The type of the vector's elements.
     */
    private final LLVMType elementType;

    /**
     * The number of the vector's elements.
     */
    private final int length;

    /**
     * @param elemType The type of the vector's elements.
     * @param len The number of the vector's elements.
     */
    public LLVMVectorType(final LLVMType elemType, final int len) {
        this.elementType = elemType;
        this.length = len;
    }

    @Override
    public boolean isAggregateType() {
        return true;
    }

    @Override
    public List<LLVMType> getSubtypes() {
        return Collections.singletonList(this.elementType);
    }

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException {
        final LLVMType elemType = this.getElementType();
        final List<LLVMLiteral> elements = new ArrayList<LLVMLiteral>();
        for (long i = 0; i < this.getLength(); i++) {
            elements.add(elemType.convertToZeroInitializedLiteral(unsigned));
        }
        return new LLVMVectorLiteral(elemType, ImmutableCreator.create(elements));
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
        final LLVMVectorType other = (LLVMVectorType) obj;
        if (this.elementType == null) {
            if (other.elementType != null) {
                return false;
            }
        } else if (!this.elementType.equals(other.elementType)) {
            return false;
        }
        if (this.length != other.length) {
            return false;
        }
        return true;
    }

    /**
     * @return The type of the vector's elements.
     */
    public LLVMType getElementType() {
        return this.elementType;
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
     * @return The number of the vector's elements.
     */
    public int getLength() {
        return this.length;
    }

    @Override
    public LLVMVectorType getThisAsVectorType() {
        return this;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.elementType == null) ? 0 : this.elementType.hashCode());
        result = prime * result + this.length;
        return result;
    }

    @Override
    public boolean isBooleanOrVecOfBooleanType() {
        return this.elementType.isBooleanType();
    }

    @Override
    public boolean isIntOrVecOfIntType() {
        return this.elementType.isIntType();
    }

    @Override
    public boolean isVectorType() {
        return true;
    }

    @Override
    public int size() {
        return this.length * this.elementType.size();
    }

    @Override
    public String toString() {
        final StringBuilder strBuilder = new StringBuilder("BasicVectorType");
        strBuilder.append(" elementType: " + this.elementType);
        strBuilder.append(" length: " + this.length);
        return strBuilder.toString();
    }

}
