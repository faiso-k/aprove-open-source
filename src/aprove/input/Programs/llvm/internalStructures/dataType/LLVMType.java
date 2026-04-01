package aprove.input.Programs.llvm.internalStructures.dataType;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public abstract class LLVMType implements Immutable, LLVMIRExport {

    //    /**
    //     * These types are a subset of the types in ParseType. Types that are
    //     * missing are not yet supported for further work. Converting not supported
    //     * ParseTypes to BasicTypes yields an error. Each subtype of BasicType has
    //     * exactly one enum type.
    //     *
    //     * These types differ slightly from types in BasicLiteral. For example
    //     * constant expressions are literals, but not types. Constant expression can
    //     * have an arbitrary type. Null is also a literal but not a type, the type
    //     * is pointer.
    //     */
    //    public enum Type {
    //        ARRAY,
    //        DOUBLE,
    //        FLOAT,
    //        FUNCTION,
    //        INT,
    //        LABEL,
    //        METADATA,
    //        NAMED,
    //        OPAQUE,
    //        PACKED_STRUCTURE,
    //        POINTER,
    //        STRUCTURE,
    //        VECTOR,
    //        VOID
    //    }

    //    /**
    //     * The type is a redundant information for faster access.
    //     */
    //    private final Type type;

    //    public BasicType(Type type) {
    //        this.type = type;
    //    }

    /**
     * This function creates a zero initialized literal of the expected
     * type. If the expected type is an integer, then an integer with value
     * 0 will be created. If the type is an array of integers, an integer
     * array initialized with zero values will be created.
     * @param unsigned Interpreted as unsigned integer?
     * @return A zero initialized literal of the current type.
     * @throws LLVMParseException If this method is called from a non-suitable type.
     */
    public abstract LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException;

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public abstract boolean equals(Object other);

    /**
     * If this type is a unnamed type, the type itself will be returned. Unnamed
     * types are, e.g., integer, float, array, structure. For named types, the type
     * which is aliased will be determined and returned if it is an unnamed
     * type, otherwise the procedure continues recursively. If the type definition is
     * recursive, this procedure remains in an infinite loop.
     *
     * Recursive type definition in C: typedef typeName1 typeName2; typedef
     * typeName2 typeName1;
     *
     * TODO check whether non-termination for recursive types is needed or at least meaningful that way
     *
     * This method must be overridden in named types.
     * @return The first type of the current type which is no named type following the type definitions in the
     *         specified module.
     */
    public LLVMType getFirstNonNamedType() {
        return this;
    }

    //    public Type getType() {
    //        return this.type;
    //    }

    /**
     * @param unsigned Interpreted as unsigned integer?
     * @param useBoundedIntegers Use bounded integers?
     * @return A general value representation for this type containing all values this type can have.
     */
    public abstract AbstractNumber getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers);

    /**
     * @param unsigned Interpreted as unsigned integer?
     * @param useBoundedIntegers Use bounded integers?
     * @return The corresponding integer type, used for arithmetic reasoning.
     */
    public abstract IntegerType getIntegerType(boolean unsigned, boolean useBoundedIntegers);

    /**
     * Must be overridden in aggregate and named types.
     * @return The subtype of this type at the specified index.
     */
    public LLVMType getSubtype() {
        throw new UnsupportedOperationException("This type has no subtypes!");
    }

    /**
     * Must be overridden in aggregate and named types.
     * @param index The index of the subtype.
     * @return The subtype of this type at the specified index.
     */
    public LLVMType getSubtype(int index) {
        throw new UnsupportedOperationException("This type has no subtypes!");
    }

    /**
     * @param indices The indices specifying the subtype.
     * @return The subtype specified by the indices.
     */
    public LLVMType getSubtype(List<LLVMLiteral> indices) {
        if (indices.isEmpty()) {
            return this;
        } else {
            if (indices.get(0) instanceof LLVMIntLiteral) {
                return this.getSubtype(indices.get(0).toInt()).getSubtype(indices.subList(1, indices.size()));
            } else {
                // index might be a variable, for example for arrays
                return this.getSubtype().getSubtype(indices.subList(1, indices.size()));
            }
        }
    }

    /**
     * Must be overridden in aggregate and named types.
     * @return A list of all subtypes of this type. This list will be empty if this is no aggregate type. Moreover, the
     *         resulting list will most probably be immutable (though this is not enforced).
     */
    public List<LLVMType> getSubtypes() {
        return Collections.emptyList();
    }

    /**
     * Must be overridden in integer and named types.
     * @return This type as integer type or null if this is no integer type.
     */
    public LLVMIntType getThisAsIntType() {
        return null;
    }

    /**
     * Must be overridden in pointer and named types.
     * @return This type as pointer type or null if this is no pointer type.
     */
    public LLVMPointerType getThisAsPointerType() {
        return null;
    }

    /**
     * Must be overridden in vector and named types.
     * @return This type as vector type or null if this is no vector type.
     */
    public LLVMVectorType getThisAsVectorType() {
        return null;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public abstract int hashCode();

    /**
     * Must be overridden in aggregate and named types.
     * @return True iff this type represents an aggregate type.
     */
    public boolean isAggregateType() {
        return false;
    }

    /**
     * Must be overridden in integer, vector, and named types.
     * @return True if this type is a boolean or vector of booleans type.
     */
    public boolean isBooleanOrVecOfBooleanType() {
        return false;
    }

    /**
     * Must be overridden in integer and named types.
     * @return True iff this type represents a boolean type.
     */
    public boolean isBooleanType() {
        return false;
    }

    /**
     * Must be overridden in integer, vector, and named types.
     * @return True if this type is an integer or vector of integers type.
     */
    public boolean isIntOrVecOfIntType() {
        return false;
    }

    /**
     * Must be overridden in integer and named types.
     * @return True iff this type represents an integer type.
     */
    public boolean isIntType() {
        return false;
    }

    /**
     * Must be overridden in integer and named types.
     * @param size The bit-width of the integer type.
     * @return True if this type is an integer type of the specified bit-width. False otherwise.
     */
    public boolean isIntTypeOfSize(int size) {
        return false;
    }

    /**
     * Must be overridden in label and named types.
     * @return True iff this type represents a label type.
     */
    public boolean isLabelType() {
        return false;
    }

    /**
     * Must be overridden in pointer and named types.
     * @return True iff this type represents a pointer type.
     */
    public boolean isPointerType() {
        return false;
    }

    /**
     * Must be overridden in recursive structure type.
     * @return True iff this type represents a recursive structure type.
     */
    public boolean isRecStructureType() {
        return false;
    }

    /**
     * Must be overridden in structure and recursive structure type.
     * @return True iff this type represents a (non-)recursive structure type.
     */
    public boolean isStructureType() {
        return false;
    }

    /**
     * Must be overridden in vector and named types.
     * @return True iff this type represents a vector type.
     */
    public boolean isVectorType() {
        return false;
    }

    /**
     * This method is overridden in BasicPointerType.
     * @param pointerSize The pointer size.
     * @return This type where pointer sizes are recursively set to the specified size.
     */
    public LLVMType setSizes(int pointerSize) {
        return this;
    }

    /**
     * @return The size of this type in bits.
     */
    public abstract int size();

	@Override
	public String toLLVMIR() {
		return "; PROPER LLVM IR OUTPUT NOT IMPLEMENTED: " + this.getClass().getName();
	}
}
