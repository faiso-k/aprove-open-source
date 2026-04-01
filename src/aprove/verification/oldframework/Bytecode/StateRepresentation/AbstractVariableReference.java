package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.math.*;

import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import immutables.*;

/**
 * An abstract variable reference just references an abstract variable.
 * @author cotto
 */
public class AbstractVariableReference implements Cloneable, Comparable<AbstractVariableReference>, Immutable {
    /**
     * The NULL reference.
     */
    public static final AbstractVariableReference NULLREF = new AbstractVariableReference("#", OperandType.ADDRESS);

    /** The prefix used to prefix all references to constant integers. */
    private static final String CONSTANT_INTEGER_PREFIX = "iconst_";

    /** The prefix used to prefix all references to constant longs. */
    private static final String CONSTANT_LONG_PREFIX = "lconst_";

    /** The prefix used to prefix all references to constant floats. */
    private static final String CONSTANT_FLOAT_PREFIX = "fconst_";

    /** The prefix used to prefix all references to constant doubles. */
    private static final String CONSTANT_DOUBLE_PREFIX = "dconst_";

    /**
     * The name of this reference.
     */
    private final String name;

    /**
     * The primitive type of the referenced value.
     */
    private final OperandType primitiveType;

    /**
     * Create a new reference to an AbstractVariable
     * @param nameParam the name of this reference
     * @param primType Primitive type of the referenced variable.
     */
    public AbstractVariableReference(final String nameParam, final OperandType primType) {
        this.name = nameParam;
        this.primitiveType = primType;
        if (this.name.equals("#") && this.primitiveType.equals(OperandType.ADDRESS)) {
            assert (AbstractVariableReference.NULLREF == null);
        }
    }

    /**
     * Create a new reference to an AbstractVariable based on a pre- existing
     * {@link AbstractVariableReference}.
     * @param ref some pre-existing variable reference
     * @return fresh variable reference of the same type as <code>ref</code>
     */
    public static AbstractVariableReference create(final AbstractVariableReference ref) {
        if (ref.isNULLRef()) {
            return AbstractVariableReference.NULLREF;
        }
        switch (ref.primitiveType) {
        case BOOLEAN:
        case CHAR:
        case BYTE:
        case SHORT:
        case INTEGER:
        case LONG:
            if (ref.pointsToConstantInt()) {
                return ref;
            }
            return new AbstractVariableReference(UIDGenerator.getIntUIDGenerator().next(), ref.primitiveType);
        case FLOAT:
        case DOUBLE:
            if (ref.name.startsWith(AbstractVariableReference.CONSTANT_FLOAT_PREFIX) || ref.name.startsWith(AbstractVariableReference.CONSTANT_DOUBLE_PREFIX)) {
                return ref;
            }
            return new AbstractVariableReference(UIDGenerator.getFloatUIDGenerator().next(), ref.primitiveType);
        case ADDRESS:
            return new AbstractVariableReference(UIDGenerator.getObjectUIDGenerator().next(), ref.primitiveType);
        case ARRAY:
            return new AbstractVariableReference(UIDGenerator.getArrayUIDGenerator().next(), ref.primitiveType);
        case VOID:
        case RETURN_ADDRESS:
        default:
            assert (false) : "Haven't implemented creation of " + ref.primitiveType + " variables yet";
            return null;
        }
    }

    /**
     * @return a new abstract variable reference with a name based on the type
     * of the given abstract variable.
     * @param primType Primitive type of the referenced variable.
     * @param var an abstract variable
     */
    public static AbstractVariableReference create(final AbstractVariable var, final OperandType primType) {
        if (var instanceof AbstractInt) {
            return AbstractVariableReference.create((AbstractInt) var, primType);
        } else if (var instanceof ObjectInstance) {
            return AbstractVariableReference.create((ObjectInstance) var, primType);
        } else if (var instanceof Array) {
            return AbstractVariableReference.create((Array) var, primType);
        } else if (var instanceof AbstractFloat) {
            return AbstractVariableReference.create((AbstractFloat) var, primType);
        } else {
            throw new NotYetImplementedException("The subtype " + var.getClass() + " is not yet implemented.");
        }
    }

    /**
     * @return a new abstract variable reference with a name based on the type
     * of the given abstract variable (here: int).
     * @param var an abstract variable
     * @param primType Primitive type of the referenced variable.
     */
    public static AbstractVariableReference create(final AbstractInt var, final OperandType primType) {
        if (var.isLiteral()) {
            final String prefix;
            if (primType == OperandType.LONG) {
                prefix = AbstractVariableReference.CONSTANT_LONG_PREFIX;
            } else {
                prefix = AbstractVariableReference.CONSTANT_INTEGER_PREFIX;
            }

            return new AbstractVariableReference(prefix + var.getLiteral(), primType);
        }
        return new AbstractVariableReference(UIDGenerator.getIntUIDGenerator().next(), primType);
    }

    /**
     * @return a new abstract variable reference with a name based on the type
     * of the given abstract variable (here: float).
     * @param var an abstract variable
     * @param primType Primitive type of the referenced variable.
     */
    public static AbstractVariableReference create(final AbstractFloat var, final OperandType primType) {
        if (var.isLiteral()) {
            final String prefix;
            if (primType == OperandType.DOUBLE) {
                prefix = AbstractVariableReference.CONSTANT_DOUBLE_PREFIX;
            } else {
                prefix = AbstractVariableReference.CONSTANT_FLOAT_PREFIX;
            }

            return new AbstractVariableReference((prefix + var.getLiteral()).replace(".", "_"), primType);
        }
        assert (!var.isLiteral());
        return new AbstractVariableReference(UIDGenerator.getFloatUIDGenerator().next(), primType);
    }

    /**
     * @return a new abstract variable reference with a name based on the type
     * of the given abstract variable (here: int).
     * @param var an abstract variable
     * @param primType Primitive type of the referenced variable.
     */
    public static AbstractVariableReference create(final ObjectInstance var, final OperandType primType) {
        if (var.isNULL()) {
            return AbstractVariableReference.NULLREF;
        }
        return new AbstractVariableReference(UIDGenerator.getObjectUIDGenerator().next(), OperandType.ADDRESS);
    }

    /**
     * @return a new abstract variable reference with a name based on the type
     * of the given abstract variable (here: array).
     * @param var an abstract variable
     */
    public static AbstractVariableReference create(final Array var, final OperandType primType) {
        return new AbstractVariableReference(UIDGenerator.getArrayUIDGenerator().next(), OperandType.ARRAY);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference clone() {
        return this;
    }

    /**
     * @return the name of this reference
     */
    @Override
    public String toString() {
        return this.name;
    }

    /**
     * @return true iff this a reference to the null pointer
     */
    public boolean isNULLRef() {
        return (this.equals(AbstractVariableReference.NULLREF));
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
        result = prime * result + ((this.primitiveType == null) ? 0 : this.primitiveType.hashCode());
        return result;
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
        final AbstractVariableReference other = (AbstractVariableReference) obj;
        if (this.name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!this.name.equals(other.name)) {
            return false;
        }
        if (this.primitiveType == null) {
            if (other.primitiveType != null) {
                return false;
            }
        } else if (!this.primitiveType.equals(other.primitiveType)) {
            return false;
        }
        return true;
    }

    @Override
    public int compareTo(final AbstractVariableReference o) {
        return this.toString().compareTo(o.toString());
    }

    /**
     * @return true iff this {@link AbstractVariableReference} points to an array
     */
    public boolean pointsToArray() {
        return this.primitiveType.equals(OperandType.ARRAY);
    }

    /**
     * @return true iff this {@link AbstractVariableReference} points to any integer type (i.e. boolean, char, byte,
     *  short, int, or long)
     */
    public boolean pointsToAnyIntegerType() {
        return this.primitiveType.equals(OperandType.BOOLEAN)
            || this.primitiveType.equals(OperandType.CHAR)
            || this.primitiveType.equals(OperandType.BYTE)
            || this.primitiveType.equals(OperandType.SHORT)
            || this.primitiveType.equals(OperandType.INTEGER)
            || this.primitiveType.equals(OperandType.LONG);
    }

    /**
     * @return true iff this {@link AbstractVariableReference} points to an integer
     */
    public boolean pointsToInteger() {
        return this.primitiveType.equals(OperandType.INTEGER);
    }

    /**
     * @return true iff this {@link AbstractVariableReference} points to a a long
     */
    public boolean pointsToLong() {
        return this.primitiveType.equals(OperandType.LONG);
    }

    /**
     * @return true iff this {@link AbstractVariableReference} points to a
     *  constant integer or long
     */
    public boolean pointsToConstantInt() {
        return (this.primitiveType.equals(OperandType.INTEGER) && this.name.startsWith(AbstractVariableReference.CONSTANT_INTEGER_PREFIX))
            || (this.primitiveType.equals(OperandType.LONG) && this.name.startsWith(AbstractVariableReference.CONSTANT_LONG_PREFIX));
    }

    /**
     * @return true iff this {@link AbstractVariableReference} points to a null,
     * a constant integer/long, a constant float/double or a return address.
     */
    public boolean pointsToConstant() {
        if (this.isNULLRef()) {
            return true;
        }
        if (this.primitiveType.equals(OperandType.INTEGER)) {
            return this.name.startsWith(AbstractVariableReference.CONSTANT_INTEGER_PREFIX);
        } else if (this.primitiveType.equals(OperandType.LONG)) {
            return this.name.startsWith(AbstractVariableReference.CONSTANT_LONG_PREFIX);
        } else if (this.primitiveType.equals(OperandType.FLOAT)) {
            return this.name.startsWith(AbstractVariableReference.CONSTANT_FLOAT_PREFIX);
        } else if (this.primitiveType.equals(OperandType.DOUBLE)) {
            return this.name.startsWith(AbstractVariableReference.CONSTANT_DOUBLE_PREFIX);
        }
        return (this instanceof ReturnAddress);
    }

    /**
     * @return true iff this {@link AbstractVariableReference} points to a float
     */
    public boolean pointsToFloat() {
        return this.primitiveType.equals(OperandType.FLOAT);
    }

    /**
     * @return true iff this {@link AbstractVariableReference} points to a float
     */
    public boolean pointsToDouble() {
        return this.primitiveType.equals(OperandType.DOUBLE);
    }

    /**
     * @return true iff this {@link AbstractVariableReference} points to an
     * instance
     */
    public boolean pointsToInstance() {
        return this.primitiveType.equals(OperandType.ADDRESS);
    }

    /**
     * @return true iff this {@link AbstractVariableReference} points to a reference type
     */
    public boolean pointsToReferenceType() {
        return this.pointsToInstance() || this.pointsToArray();
    }

    /**
     * @return the primitive type of this reference.
     */
    public OperandType getPrimitiveType() {
        return this.primitiveType;
    }

    public SemiRingDomain<?> getSemiRingDomain() {
        if (this.pointsToAnyIntegerType()) {
            return DomainFactory.INTEGERS;
        } else if (this.pointsToInstance()) {
            return DomainFactory.UNKNOWN;
        } else if (this.pointsToArray()) {
            return DomainFactory.UNKNOWN;
        } else if (this.pointsToFloat() || this.pointsToDouble()) {
            return DomainFactory.UNKNOWN;
        } else {
            assert (false) : "Haven't implemented domains for " + this.primitiveType + " variables yet";
            return null;
        }
    }

    /**
     * @return the LiteralInt corresponding to the constant integer encoded
     *  in the ref name. Breaks if used on non-constant ints or non-ints.
     */
    public LiteralInt toLiteralInt() {
        assert (this.pointsToConstantInt()) : "Can only generate literal int for constant int reference";
        if (this.name.startsWith(AbstractVariableReference.CONSTANT_LONG_PREFIX)) {
            return AbstractInt.create(new BigInteger(this.name.substring(AbstractVariableReference.CONSTANT_LONG_PREFIX.length())));
        }
        assert (this.name.startsWith(AbstractVariableReference.CONSTANT_INTEGER_PREFIX));
        return AbstractInt.create(new BigInteger(this.name.substring(AbstractVariableReference.CONSTANT_INTEGER_PREFIX.length())));
    }

    /**
     * @param varPrefix a String that is prepended to the generated variable's
     *  name.
     * @return a SMTLIB variable corresponding to this.
     */
    public SMTLIBIntValue toSMTIntValue(final String varPrefix) {
        assert (this.pointsToAnyIntegerType()) : "Cannot generate SMTLIBIntValue for non-integer reference";
        if (this.name.startsWith(AbstractVariableReference.CONSTANT_LONG_PREFIX)) {
            return SMTLIBIntConstant.create(new BigInteger(this.name.substring(AbstractVariableReference.CONSTANT_LONG_PREFIX.length())));
        } else if (this.name.startsWith(AbstractVariableReference.CONSTANT_INTEGER_PREFIX)) {
            return SMTLIBIntConstant.create(new BigInteger(this.name.substring(AbstractVariableReference.CONSTANT_INTEGER_PREFIX.length())));
        }
        return SMTLIBIntVariable.create(varPrefix + "_" + this.name);
    }

    public boolean pointsToAnyFloatType() {
        return this.primitiveType.equals(OperandType.FLOAT) || this.primitiveType.equals(OperandType.DOUBLE);
    }
}
