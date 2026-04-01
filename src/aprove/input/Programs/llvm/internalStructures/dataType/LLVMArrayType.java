package aprove.input.Programs.llvm.internalStructures.dataType;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMArrayType extends LLVMType {

    /**
     * The type of the array's elements.
     */
    private final LLVMType elementType;

    /**
     * The number of entries in this array.
     */
    private final int length;

    /**
     * @param elemType The type of the array's elements.
     * @param len The number of entries in this array.
     */
    public LLVMArrayType(LLVMType elemType, int len) {
        this.elementType = elemType;
        this.length = len;
    }

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException {
        final LLVMType elemType = this.getElementType();
        final List<LLVMLiteral> elements = new ArrayList<LLVMLiteral>();
        for (int i = 0; i < this.getLength(); i++) {
            elements.add(elemType.convertToZeroInitializedLiteral(unsigned));
        }
        return new LLVMArrayLiteral(ImmutableCreator.create(elements), elemType);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof LLVMArrayType)) {
            return false;
        }
        final LLVMArrayType other = (LLVMArrayType) obj;
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
     * @return The type of the array's elements.
     */
    public LLVMType getElementType() {
        return this.elementType;
    }

    @Override
    public AbstractBoundedInt getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        if (useBoundedIntegers) {
            throw new UnsupportedOperationException("Not yet implemented for this type.");
        } else {
            return AbstractBoundedInt.getUnknown(IntegerType.UNBOUND);
        }
    }

    @Override
    public IntegerType getIntegerType(boolean unsigned, boolean useBoundedIntegers) {
        // TODO implement
        return null;
    }

    /**
     * @return The number of entries in this array.
     */
    public int getLength() {
        return this.length;
    }

    @Override
    public LLVMType getSubtype() {
        return this.elementType;
    }

    @Override
    public LLVMType getSubtype(int index) {
        if (0 > index) {
            throw new IllegalArgumentException("Index is negative!");
        }
        if (index >= this.length) {
            throw new IllegalArgumentException("Index is out of bounds!");
        }
        return this.elementType;
    }

    @Override
    public List<LLVMType> getSubtypes() {
        return Collections.singletonList(this.elementType);
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
    public boolean isAggregateType() {
        return true;
    }

    @Override
    public int size() {
        return this.length * this.elementType.size();
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append("[");
        res.append(this.length);
        res.append(" x ");
        res.append(this.elementType);
        res.append("]");
        return res.toString();
    }

}
