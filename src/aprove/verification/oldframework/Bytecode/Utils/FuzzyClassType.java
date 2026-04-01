package aprove.verification.oldframework.Bytecode.Utils;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * Representation of (yet) unspecified class types. In all cases, the minimal
 * type is known (which is always at least java.lang.Object, but might be something
 * more specialized) and sometimes, we also know that no further specialization
 * can happen.
 *
 * @author Marc Brockschmidt
 */
public final class FuzzyClassType extends FuzzyType {
    /**
     * Cloneable
     */
    public static final FuzzyClassType FT_JAVA_LANG_CLONEABLE = new FuzzyClassType(
        JAVA_LANG_CLONEABLE.getClassName(),
        true);

    /**
     * Serializable
     */
    public static final FuzzyClassType FT_JAVA_LANG_SERIALIZABLE = new FuzzyClassType(
        JAVA_IO_SERIALIZABLE.getClassName(),
        true);

    /**
     * The String class.
     */
    public static final FuzzyClassType FT_JAVA_LANG_STRING = new FuzzyClassType(JAVA_LANG_STRING.getClassName(), true);

    /**
     * The Class class.
     */
    public static final FuzzyClassType FT_JAVA_LANG_CLASS = new FuzzyClassType(JAVA_LANG_CLASS.getClassName(), true);

    /**
     * The Object class.
     */
    public static final FuzzyClassType FT_JAVA_LANG_OBJECT = new FuzzyClassType(JAVA_LANG_OBJECT.getClassName(), true);

    /**
     * Indicates whether the set of classes described by the instance contains
     * exactly the class specified by minimalClass.
     */
    private final boolean isConcrete;

    /**
     * Minimal class an object with this FuzzyType will have.
     */
    private final ClassName minimalClass;

    /**
     * @param minClass Minimal type an object with this FuzzyType will have.
     * @param isConcreteParam Indicates whether the fuzzy class is concrete or
     * abstract (see isConcrete)
     */
    public FuzzyClassType(final ClassName minClass, final boolean isConcreteParam) {
        this(minClass, isConcreteParam, 0);
    }

    /**
     * @param minClass Minimal type an object with this FuzzyType will have.
     * @param isConcreteParam Indicates whether the fuzzy class is concrete or abstract
     * (see isConcrete)
     * @param arrayDimParam Dimension of this array (0 for non-array objects)
     */
    public FuzzyClassType(final ClassName minClass, final boolean isConcreteParam, final int arrayDimParam) {
        super(arrayDimParam, 'L' + minClass.toSlashed() + ';');
        this.minimalClass = minClass;
        this.isConcrete = isConcreteParam;
    }

    /**
     * NOTE: DO NOT USE THIS. It's a construct for elegant get(Enclosed|Innermost)Type
     *  implementation.
     * @param outerType pre-existing outer fuzzy class type from which to take all information but
     *  the array dimension
     * @param arrayDim Dimension of this array (0 for non-array objects)
     */
    public FuzzyClassType(final FuzzyClassType outerType, final int arrayDim) {
        this(outerType.minimalClass, outerType.isConcrete, arrayDim);
    }

    /**
     * @param typeSig String to parse from
     * @param arrayDim pre-parsed array dimension
     * @return a fresh FuzzyType object holding the type of the first
     * type in the parsed string
     */
    public static FuzzyClassType parseTypeSignatures(final String typeSig, final int arrayDim) {
        if (typeSig.startsWith("L")) {
            return new FuzzyClassType(ClassName.fromSlashed(typeSig.substring(1, typeSig.indexOf(";"))), true, arrayDim);
        }
        throw new RuntimeException("Not a class type signature: " + typeSig);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (!(obj instanceof FuzzyClassType)) {
            return false;
        }
        final FuzzyClassType other = (FuzzyClassType) obj;
        if (this.isConcrete != other.isConcrete) {
            return false;
        }
        if (this.minimalClass == null) {
            if (other.minimalClass != null) {
                return false;
            }
        } else if (!this.minimalClass.equals(other.minimalClass)) {
            return false;
        }
        return true;
    }

    /**
     * Expand this type. All results are concrete, apart from arrays introduced
     * by expanding Object/Serializable/Cloneable.
     * @param res add the results here
     * @param cPath The considered class path for this analysis.
     */
    @Override
    public void expand(final Set<FuzzyType> res, final ClassPath cPath, JBCOptions options) {
        if (this.isConcrete()) {
            res.add(this);
        } else {
            // expand according to the type tree
            final TypeTree tree = cPath.getTypeTree(this);
            assert (tree != null) : this.getMinimalClass();
            for (final TypeTree subType : tree.expand(options)) {
                if (!subType.isAbstract()) {
                    res.add(new FuzzyClassType(subType.getClassName(), true, this.getArrayDimension()));
                }
            }

            // expand to arrays (e.g. Object... to [Object...)
            this.expandToArrays(res);
        }
    }

    /**
     * Expand this type to arrays, if possible (for
     * Object/Serializable/Cloneable).
     * @param res add the resulting types here
     */
    public void expandToArrays(final Set<FuzzyType> res) {
        if (this.isArrayParentClass()) {
            // jlO... can mean [jlO...
            res.add(new FuzzyClassType(JAVA_LANG_OBJECT.getClassName(), false, this.getArrayDimension() + 1));

            // jlO... can mean [I or [B or ...
            for (final OperandType operandType : OperandType.values()) {
                if (operandType.isPrimitive()) {
                    res.add(new FuzzyPrimitiveType(operandType, this.getArrayDimension() + 1));
                }
            }
        }
    }

    /**
     * @return the type of variables enclosed in this array
     */
    @Override
    public FuzzyType getEnclosedType() {
        assert (this.isArrayType()) : "Trying to get enclosed type of non-array";
        return new FuzzyClassType(this, this.getArrayDimension() - 1);
    }

    /**
     * @return the type of an enclosing array
     */
    @Override
    public FuzzyType getEnclosingType() {
        return new FuzzyClassType(this, this.getArrayDimension() + 1);
    }

    /**
     * @return the innermost type of variables enclosed in this array:
     */
    @Override
    public FuzzyType getInnermostType() {
        super.getInnermostType();
        return new FuzzyClassType(this, 0);
    }

    /**
     * @return the minimalClass
     */
    public ClassName getMinimalClass() {
        return this.minimalClass;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getUsedWords() {
        if (this.isArrayType()) {
            return OperandType.ARRAY.getWords();
        }
        return OperandType.ADDRESS.getWords();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + (this.isConcrete ? 1231 : 1237);
        result = prime * result + ((this.minimalClass == null) ? 0 : this.minimalClass.hashCode());
        return result;
    }

    /**
     * @return True iff the instance does not describe a concrete class
     */
    public boolean isAbstract() {
        return !this.isConcrete();
    }

    /**
     * @return true iff this a class which is parent type of arrays with a higher dimension.
     */
    public boolean isArrayParentClass() {
        return (this.minimalClass.equals(JAVA_LANG_OBJECT.getClassName())
            || this.minimalClass.equals(JAVA_IO_SERIALIZABLE.getClassName()) || this.minimalClass
                .equals(JAVA_LANG_CLONEABLE.getClassName()));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Boolean isAssignmentCompatibleTo(final FuzzyType targetT, final ClassPath cPath) {
        final FuzzyClassType subjectS = this;
        if (subjectS.isArrayType()) {
            if (targetT.isArrayType()) {
                // we are dealing with [x and [y, so just have a look at x and y
                final FuzzyType subjectComponent = subjectS.getEnclosedType();
                final FuzzyType targetComponent = targetT.getEnclosedType();
                if (targetComponent instanceof FuzzyPrimitiveType) {
                    // only one primitive? [Object vs. [int? Does not work.
                    return false;
                }

                // no primitives, just recurse
                return subjectComponent.isAssignmentCompatibleTo(targetComponent, cPath);
            }
            // class or interface type: jlO, jiS, jlC
            assert (targetT instanceof FuzzyClassType);
            final FuzzyClassType fcT = (FuzzyClassType) targetT;
            if (!fcT.isConcrete) {
                return null;
            }
            // all arrays extend/implement these three classes/interfaces
            return ((FuzzyClassType) targetT).isArrayParentClass();
        } else if (targetT.isArrayType()) {
            //If this no array type, we can never assign it to a value of an array type
            return false;
        }
        /*
         * No arrays are involved, furthermore this opcode is only involved
         * with non-primitives. As a result, we can just use the instanceOf
         * method of type trees.
         */
        if (targetT instanceof FuzzyClassType) {
            final FuzzyClassType fcT = (FuzzyClassType) targetT;
            final TypeTree typeTreeT = cPath.getTypeTree((FuzzyClassType) targetT);
            final TypeTree typeTreeS = cPath.getTypeTree(subjectS);
            final boolean instanceOf = typeTreeS.instanceOf(typeTreeT);
            if (instanceOf && !fcT.isConcrete) {
                return null;
            }
            return instanceOf;
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isConcrete() {
        return this.isConcrete;
    }

    /**
     * @return this type as X..., even if this is X|.
     */
    public FuzzyClassType toAbstract() {
        if (this.isAbstract()) {
            return this;
        }
        return new FuzzyClassType(this.minimalClass, false, this.getArrayDimension());
    }

    /**
     * @return this type as X|, even if this is X....
     */
    public FuzzyClassType toConcrete() {
        if (this.isConcrete()) {
            return this;
        }
        return new FuzzyClassType(this.minimalClass, true, this.getArrayDimension());
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
        sb.append(this.minimalClass);
        if (!this.isConcrete) {
            sb.append("...");
        } else {
            sb.append("|");
        }
        for (int i = 0; i < this.getArrayDimension(); i++) {
            sb.append("]");
        }
    }

    /** {@inheritDoc} */
    @Override
    public String binaryNameInArray() {
        return "L" + this.minimalClass.toString() + ";";
    }

    /** {@inheritDoc} */
    @Override
    public String binaryNameWithoutArray() {
        return this.minimalClass.toString();
    }
}
