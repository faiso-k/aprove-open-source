package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * Representation of (yet) unspecified types. These can either be class types, or
 * arrays of any (primitive and non-primitive) type.
 *
 * @author Marc Brockschmidt
 */
public abstract class FuzzyType {
    /**
     * Array dimension. Zero for non-array objects.
     */
    private final int arrayDimension;

    /**
     * Type descriptor for this fuzzy type, only used for debugging.
     */
    private String typeDescriptor;

    /**
     * Binary name of this type.
     */
    private String binaryName;

    /**
     * the type descriptor of the type contained inside the array of this type
     */
    private final String innerTypeDescriptor;

    /**
     * Default constructor.
     * @param arrayDim Dimension of this array (0 for non-array objects)
     * @param innerTypeDescriptorParam the type descriptor of the type contained
     * inside the array of this type
     */
    protected FuzzyType(final int arrayDim, final String innerTypeDescriptorParam) {
        this.arrayDimension = arrayDim;
        this.innerTypeDescriptor = innerTypeDescriptorParam;
    }

    /**
     * Counts the occurences of "[" at the beginning of a string, which
     * usually corresponds to the array depth of the following type.
     * @param string Some type information encoded as string
     * @return number of "[" at the beginning of the string.
     */
    private static int countArrayRefs(final String string) {
        int n = 0;
        while (string.charAt(n) == '[') {
            n++;
        }

        return n;
    }

    /**
     * @return the fuzzy type for some array type descriptor [[..[x, where x is
     * the type descriptor of some non-array type followed by an arbitrary
     * string (which is ignored)
     * @param typeSig the type descriptor string of some array type.
     */
    private static FuzzyType parseArrayTypeDescriptor(final String typeSig) {
        assert (typeSig.charAt(0) == '[');
        final int parsedArrayDim = FuzzyType.countArrayRefs(typeSig);
        //After i + parsedArrayDim, the description of the type contained in the array follows:
        return FuzzyType.parseNonArrayTypeDescriptor(typeSig.substring(parsedArrayDim), parsedArrayDim);
    }

    /**
     * @return the fuzzy type for some non-array type descriptor which is nested
     * in an array of given dimension (may be 0)
     * @param typeSig the type descriptor string of some non-array type
     * (followed by an arbitrary string, which is ignored)
     * @param arrayDim the array dimension outside the given type
     */
    private static FuzzyType parseNonArrayTypeDescriptor(final String typeSig, final int arrayDim) {
        final char character = typeSig.charAt(0);
        assert (character != '[');
        if (character == 'L') {
            return FuzzyClassType.parseTypeSignatures(typeSig, arrayDim);
        }
        return FuzzyPrimitiveType.parseTypeSignatures(typeSig, arrayDim);
    }

    /**
     * <b>This should <i>only</i> be used with type signatures formed as
     * described below, not with normal type signatures</b>
     *
     * This is a special case parser for constant pool entries pointed at
     * from castcheck or instanceof opcodes. In this case, the entry
     * is either a normal type signature of an array (e.g. [Ljava/langObject;),
     * or it is just a fully qualified classname (e.g. java/lang/Object).
     * Both are parsed correctly.
     *
     * @param typeString String form of type signature to parse from
     * @return a fresh FuzzyType object holding the type of the first
     * type in the parsed string
     */
    public static FuzzyType parseType(final String typeString) {
        /*
         * Two possible cases here:
         *  a) typeString contains a fully qualified classname
         *  b) typeString describes an array of something
         */
        if (typeString.charAt(0) == '[') {
            // case b
            return FuzzyType.parseTypeDescriptor(typeString);
        }
        // case a
        return new FuzzyClassType(ClassName.fromSlashed(typeString), true);
    }

    /**
     * @param typeSig String form of type signature to parse from
     * @return a fresh FuzzyType object holding the type of the first
     * type in the parsed string
     */
    public static FuzzyType parseTypeDescriptor(final String typeSig) {
        if (typeSig.charAt(0) == '[') {
            return FuzzyType.parseArrayTypeDescriptor(typeSig);
        }
        return FuzzyType.parseNonArrayTypeDescriptor(typeSig, 0);
    }

    /**
     * {@inheritDoc}
     */
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
        final FuzzyType other = (FuzzyType) obj;
        if (this.arrayDimension != other.arrayDimension) {
            return false;
        }
        return true;
    }

    /**
     * Expand this fuzzy type add and the results to the given set. All added
     * types are concrete, apart from arrays introduced by expanding
     * Object/Serializable/Cloneable.
     * @param res add the results here
     * @param cPath The considered class path for this analysis.
     */
    public abstract void expand(Set<FuzzyType> res, final ClassPath cPath, JBCOptions options);

    /**
     * @return the array dimension
     */
    public int getArrayDimension() {
        return this.arrayDimension;
    }

    /**
     * @return the type of variables enclosed in this array
     */
    public abstract FuzzyType getEnclosedType();

    /**
     * @return the type of an enclosing array.
     */
    public abstract FuzzyType getEnclosingType();

    /**
     * @return the innermost type of variables enclosed in this array:
     */
    public FuzzyType getInnermostType() {
        assert (this.isArrayType()) : "Trying to get enclosed type of non-array";
        return null;
    }

    /**
     * @return the primitiveType
     */
    public OperandType getPrimitiveType() {
        if (this.isArrayType()) {
            return OperandType.ARRAY;
        } else if (this instanceof FuzzyClassType) {
            return OperandType.ADDRESS;
        } else if (this instanceof FuzzyPrimitiveType) {
            return ((FuzzyPrimitiveType) this).getOperandType();
        } else {
            throw new RuntimeException("Unknown fuzzy type implementation: " + this);
        }
    }

    /**
     * @return the descriptor of this type
     */
    public String getTypeDescriptor() {
        if (this.typeDescriptor == null) {
            final StringBuilder sb = new StringBuilder();
            for (int i = 0; i < this.arrayDimension; i++) {
                sb.append('[');
            }
            sb.append(this.innerTypeDescriptor);
            this.typeDescriptor = sb.toString();
        }

        return this.typeDescriptor;
    }

    /**
     * @return The number of used slots (words) in, e.g. the opstack
     */
    public abstract int getUsedWords();

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        int result = 1;
        result = 31 * result + this.arrayDimension;
        return result;
    }

    /**
     * @return true iff this is an array type
     */
    public boolean isArrayType() {
        return (this.arrayDimension > 0);
    }

    /**
     * Check if this can be cast/assigned to to the target. This only checks
     * reference types and must not be used for primitive types!
     * @param targetT the type that subjectS is cast to or checked against
     * @param cPath The considered class path for this analysis.
     * @return true if the cast/instanceof succeeds, false if it does not, null
     * if we have no clue.
     * @see JVMS aastore description
     */
    public abstract Boolean isAssignmentCompatibleTo(final FuzzyType targetT, final ClassPath cPath);

    /**
     * @return true iff the instance describes a concrete class
     */
    public abstract boolean isConcrete();

    /**
     * Writes a nice string representation to the argument {@link StringBuilder}
     * @param sb some {@link StringBuilder} to write to
     */
    public abstract void toString(final StringBuilder sb);

    /**
     * @return the length of the type signature needed to describe this fuzzy type
     */
    public int typeSignatureLength() {
        return this.getTypeDescriptor().length();
    }

    /**
     * @return the name of this when used in an array, i.e. "I" for "int" and
     *  "Ljava.lang.Object;" for jlO.
     */
    public abstract String binaryNameInArray();

    /**
     * @return the name of this when not used in an array, i.e. "int" for "int"
     * and "java.lang.Object" for jlO.
     */
    public abstract String binaryNameWithoutArray();

    /**
     * Create and return the binary name of a type. Examples:
     *  - java.lang.String has binary name "java.lang.String"
     *  - java.lang.String[] has binary name "[Ljava.lang.String;"
     *  - int has binary name "int"
     *  - int[][][] has binary name "[[[I"

     * @return the binary name of this type.
     */
    public String toBinaryName() {
        assert (this.isConcrete()) : "Trying to get binary name of non-concrete type " + this.toString();

        if (this.binaryName == null) {
            if (this.getArrayDimension() > 0) {
                final StringBuilder sb = new StringBuilder();
                for (int i = 0; i < this.getArrayDimension(); i++) {
                    sb.append("[");
                }
                sb.append(this.binaryNameInArray());
                this.binaryName = sb.toString();
            } else {
                this.binaryName = this.binaryNameWithoutArray();
            }
        }

        return this.binaryName;
    }
}
