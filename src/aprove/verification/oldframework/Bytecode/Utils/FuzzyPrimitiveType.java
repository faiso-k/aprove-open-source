package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;

/**
 * This class is used to represent primitive types and types where primitives
 * are stored in some n-dimensional array.
 * @author Marc Brockschmidt
 */
public final class FuzzyPrimitiveType extends FuzzyType {
    /**
     * Primitive data type of an array.
     */
    private final OperandType primitiveType;

    /**
     * @param character the character used to define the primitive type in field
     * descriptors
     * @param arrayDim Dimension of this array (0 for non-array objects)
     */
    public FuzzyPrimitiveType(final char character, final int arrayDim) {
        super(arrayDim, Character.toString(character));
        this.primitiveType = OperandType.fromCharacter(character);
    }

    /**
     * NOTE: DO NOT USE THIS. It's a construct for elegant get(Enclosed|Innermost)Type
     *  implementation.
     * @param outerType pre-existing outer fuzzy primitive type from which to take all
     *  information but the array dimension
     * @param arrayDim Dimension of this array (0 for non-array objects)
     */
    private FuzzyPrimitiveType(final FuzzyPrimitiveType outerType,
            final int arrayDim) {
        super(arrayDim,
            Character.toString(outerType.primitiveType.getCharacter()));
        this.primitiveType = outerType.primitiveType;
    }

    /**
     * @param primType Primitive type of the array.
     * @param arrayDim Dimension of this array (0 for non-array objects)
     */
    public FuzzyPrimitiveType(final OperandType primType, final int arrayDim) {
        super(arrayDim, Character.toString(primType.getCharacter()));
        this.primitiveType = primType;

    }

    /**
     * @param typeSig String to parse from
     * @param arrayDim pre-parsed array dimension
     * @return a fresh FuzzyType object holding the type of the first
     * type in the parsed string
     */
    public static FuzzyPrimitiveType parseTypeSignatures(final String typeSig, final int arrayDim) {
        final char character = typeSig.charAt(0);
        return new FuzzyPrimitiveType(character, arrayDim);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (!(obj instanceof FuzzyPrimitiveType)) {
            return false;
        }
        final FuzzyPrimitiveType other = (FuzzyPrimitiveType) obj;
        if (this.primitiveType == null) {
            if (other.primitiveType != null) {
                return false;
            }
        } else if (!this.primitiveType.equals(other.primitiveType)) {
            return false;
        }
        return true;
    }

    /**
     * FuzzyPrimitiveTypes cannot be expanded, so just add this.
     * @param res add this here
     * @param cPath The considered class path for this analysis.
     */
    @Override
    public void expand(final Set<FuzzyType> res, final ClassPath cPath, JBCOptions options) {
        res.add(this);
    }

    /**
     * @return the type of variables enclosed in this array
     */
    @Override
    public FuzzyType getEnclosedType() {
        assert (this.isArrayType()) : "Trying to get enclosed type of non-array";
        return new FuzzyPrimitiveType(this, this.getArrayDimension() - 1);
    }

    /**
     * @return the type of an enclosing array
     */
    @Override
    public FuzzyType getEnclosingType() {
        return new FuzzyPrimitiveType(this, this.getArrayDimension() + 1);
    }

    /**
     * @return the innermost type of variables enclosed in this array:
     */
    @Override
    public FuzzyType getInnermostType() {
        super.getInnermostType();
        return new FuzzyPrimitiveType(this, 0);
    }

    /**
     * @return the primitiveType
     */
    public OperandType getOperandType() {
        return this.primitiveType;
    }

    @Override
    public int getUsedWords() {
        if (this.isArrayType()) {
            return OperandType.ARRAY.getWords();
        }
        return this.primitiveType.getWords();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result =
            prime
                * result
                + ((this.primitiveType == null) ? 0
                    : this.primitiveType.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Boolean isAssignmentCompatibleTo(final FuzzyType targetT,
        final ClassPath cPath) {
        if (targetT instanceof FuzzyClassType) {
            final FuzzyClassType targetClassT = (FuzzyClassType) targetT;
            assert (!targetClassT.isAbstract());
            //If the array dimension is smaller and arrays are instances of
            //the target class, we are fine:
            if (targetClassT.getArrayDimension() < this.getArrayDimension()
                    && targetClassT.isArrayParentClass()) {
                return Boolean.TRUE;
            }
            //Otherwise, this won't work:
            return Boolean.FALSE;
        //Both are primitive arrays, so check if the array dimension matches
        //and the enclosed primitive types are the same.
        }
        assert (targetT instanceof FuzzyPrimitiveType);
        final FuzzyPrimitiveType targetPrimitiveT =
            (FuzzyPrimitiveType) targetT;
        return (targetPrimitiveT.getArrayDimension() == this.getArrayDimension() && targetPrimitiveT.getPrimitiveType() == this.getPrimitiveType());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isConcrete() {
        return true;
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb);
        return sb.toString();
    }

    /**
     * Writes a nice string representation to the argument {@link StringBuilder};
     * @param sb some {@link StringBuilder} to write to
     */
    @Override
    public void toString(final StringBuilder sb) {
        for (int i = 0; i < this.getArrayDimension(); i++) {
            sb.append("[");
        }
        sb.append(this.primitiveType.toString());
        for (int i = 0; i < this.getArrayDimension(); i++) {
            sb.append("]");
        }
    }

    /** {@inheritDoc} */
    @Override
    public String binaryNameInArray() {
        return String.valueOf(this.primitiveType.getCharacter());
    }

    /** {@inheritDoc} */
    @Override
    public String binaryNameWithoutArray() {
        return this.primitiveType.getShortName();
    }
}
