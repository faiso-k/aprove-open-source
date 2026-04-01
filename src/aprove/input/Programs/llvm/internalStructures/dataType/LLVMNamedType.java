package aprove.input.Programs.llvm.internalStructures.dataType;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * A named type which represents a type, but may has to be resolved later.
 * @author Janine Repke, cryingshadow
 * @version $Id$
 */
public class LLVMNamedType extends LLVMType {

    /**
     * The type referenced by this type.
     */
    private final LLVMType type;

    /**
     * The name of this type.
     */
    private final String typeName;

    /**
     * @param name Name of the type without leading %-sign.
     * @param namedType The type referenced by the specified type name.
     */
    public LLVMNamedType(final String name, final LLVMType namedType) {
        this.typeName = name;
        this.type = namedType;
    }

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException {
        return this.getFirstNonNamedType().convertToZeroInitializedLiteral(unsigned);
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
        final LLVMNamedType other = (LLVMNamedType) obj;
        if (!this.typeName.equals(other.typeName)) {
            return false;
        }
        if (!this.type.equals(other.type)) {
            return false;
        }
        return true;
    }

    @Override
    public LLVMType getFirstNonNamedType() {
        return this.type.getFirstNonNamedType();
    }

    @Override
    public AbstractNumber getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        return this.type.getInitializedIntValue(unsigned, useBoundedIntegers);
    }

    @Override
    public IntegerType getIntegerType(boolean unsigned, boolean useBoundedIntegers) {
        // TODO implement correctly
        return IntegerType.UI64;
    }

    @Override
    public LLVMType getSubtype(final int index) {
        return this.type.getSubtype(index);
    }

    @Override
    public LLVMIntType getThisAsIntType() {
        return this.type.getThisAsIntType();
    }

    @Override
    public LLVMPointerType getThisAsPointerType() {
        return this.type.getThisAsPointerType();
    }

    @Override
    public LLVMVectorType getThisAsVectorType() {
        return this.type.getThisAsVectorType();
    }

    /**
     * @return The type referenced by this named type.
     */
    public LLVMType getType() {
        return this.type;
    }

    /**
     * @return The name of this type.
     */
    public String getTypeName() {
        return this.typeName;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.typeName == null) ? 0 : this.typeName.hashCode());
        return result + ((this.type == null) ? 0 : this.type.hashCode());
    }

    @Override
    public boolean isBooleanOrVecOfBooleanType() {
        return this.type.isBooleanOrVecOfBooleanType();
    }

    @Override
    public boolean isBooleanType() {
        return this.type.isBooleanType();
    }

    @Override
    public boolean isIntOrVecOfIntType() {
        return this.type.isIntOrVecOfIntType();
    }

    @Override
    public boolean isIntType() {
        return this.type.isIntType();
    }

    @Override
    public boolean isIntTypeOfSize(final int size) {
        return this.type.isIntTypeOfSize(size);
    }

    @Override
    public boolean isLabelType() {
        return this.type.isLabelType();
    }

    @Override
    public boolean isPointerType() {
        return this.type.isPointerType();
    }

    @Override
    public boolean isVectorType() {
        return this.type.isVectorType();
    }

    @Override
    public boolean isAggregateType() {
        return this.type.isAggregateType();
    }

    @Override
    public List<LLVMType> getSubtypes() {
        return this.type.getSubtypes();
    }

    @Override
    public int size() {
        return this.type.size();
    }

    @Override
    public String toString() {
        final StringBuilder strBuilder = new StringBuilder("BasicTypeName");
        strBuilder.append(" typeName: " + this.typeName);
        strBuilder.append(this.type);
        return strBuilder.toString();
    }

}
