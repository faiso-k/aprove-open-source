package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;

import aprove.verification.oldframework.IntegerReasoning.*;
import immutables.*;

/**
 * Representation of the bounds of integer-type values such as "char", "int", ...
 * @author Marc Brockschmidt, cryingshadow
 */
public final class IntegerType implements Immutable {

    /**
     * The 1 bit integer type.
     */
    public static final IntegerType I1;

    /**
     * The signed 16 bit integer type.
     */
    public static final IntegerType I16;

    /**
     * The signed 32 bit integer type.
     */
    public static final IntegerType I32;

    /**
     * The signed 64 bit integer type.
     */
    public static final IntegerType I64;

    /**
     * The signed 8 bit integer type.
     */
    public static final IntegerType I8;

    /**
     * What Java considers to be an "int".
     */
    public static final IntegerType JAVA_INT;

    /**
     * What Java considers to be a "long".
     */
    public static final IntegerType JAVA_LONG;

    /**
     * The unsigned 8 bit integer type.
     */
    public static final IntegerType UI16;

    /**
     * The unsigned 8 bit integer type.
     */
    public static final IntegerType UI32;

    /**
     * The unsigned 8 bit integer type.
     */
    public static final IntegerType UI64;

    /**
     * The unsigned 8 bit integer type.
     */
    public static final IntegerType UI8;

    /**
     * The unbound integer type, corresponding to the mathematical numbers.
     */
    public static final IntegerType UNBOUND;

    /**
     * The unbound non-negative integer type, corresponding to the natural numbers in computer science.
     */
    public static final IntegerType UNBOUND_NON_NEGATIVE;

    /**
     * The unbound positive integer type, corresponding to the mathematical natural numbers.
     */
    public static final IntegerType UNBOUND_POSITIVE;

    static {
        I1 = new IntegerType(1, false);
        I16 = new IntegerType(16, true);
        I32 = new IntegerType(32, true);
        I64 = new IntegerType(64, true);
        I8 = new IntegerType(8, true);
        UI16 = new IntegerType(16, false);
        UI32 = new IntegerType(32, false);
        UI64 = new IntegerType(64, false);
        UI8 = new IntegerType(8, false);
        UNBOUND = new IntegerType(IntervalBound.NEGINF, IntervalBound.POSINF);
        UNBOUND_NON_NEGATIVE = new IntegerType(IntervalBound.ZERO, IntervalBound.POSINF);
        UNBOUND_POSITIVE = new IntegerType(IntervalBound.ONE, IntervalBound.POSINF);
        JAVA_INT = IntegerType.I32;
        JAVA_LONG = IntegerType.I64;
    }

    /**
     * The number of bits used to represent this type.
     */
    private final int bitSize;

    /**
     * Lower bound of this integer type (cached).
     */
    private final IntervalBound lower;

    /**
     * Number of representable values (cached).
     */
    private final BigInteger numberOfValues;

    /**
     * Flag deciding if one bit is used to indicate the sign or not.
     */
    private final boolean signed;

    /**
     * Upper bound of this integer type (cached).
     */
    private final IntervalBound upper;

    /**
     * @param bits The number of bits used to represent this type.
     * @param sign Flag deciding if one bit is used to indicate the sign or not.
     */
    public IntegerType(int bits, boolean sign) {
        this.bitSize = bits;
        this.signed = sign;
        this.lower = IntervalBound.create(IntegerUtils.lowerLimitForBoundedInt(bits, sign));
        this.upper = IntervalBound.create(IntegerUtils.upperLimitForBoundedInt(bits, sign));
        this.numberOfValues = BigInteger.valueOf(2).pow(bits);
    }

    /**
     * @param l lower bound
     * @param u upper bound
     */
    private IntegerType(IntervalBound l, IntervalBound u) {
        this.bitSize = 0;
        this.signed = true;
        this.lower = l;
        this.upper = u;
        this.numberOfValues = null;
    }

    /**
     * @param i some (abstract) integer
     * @return checks if the chosen values are representable by this type.
     */
    public boolean canRepresent(AbstractBoundedInt i) {
        if ((this.lower.isFinite() && i.getLower().compareTo(this.lower) < 0)
            || (this.upper.isFinite() && i.getUpper().compareTo(this.upper) > 0))
        {
            return false;
        }
        return true;
    }

    /**
     * @param i some (abstract) integer
     * @return checks if the chosen values are representable by this type.
     */
    public boolean canRepresent(AbstractInt i) {
        if ((this.lower.isFinite() && i.getLower().compareTo(this.lower) < 0)
            || (this.upper.isFinite() && i.getUpper().compareTo(this.upper) > 0))
        {
            return false;
        }
        return true;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof IntegerType)) {
            return false;
        }
        final IntegerType other = (IntegerType) obj;
        if (this.lower == null) {
            if (other.lower != null) {
                return false;
            }
        } else if (!this.lower.equals(other.lower)) {
            return false;
        }
        if (this.upper == null) {
            if (other.upper != null) {
                return false;
            }
        } else if (!this.upper.equals(other.upper)) {
            return false;
        }
        return true;
    }

    /**
     * @return The number of bits used to represent this type.
     */
    public int getBitSize() {
        assert (this.bitSize > 0) : "Trying to get bit size of unbounded int";
        return this.bitSize;
    }

    /**
     * @return Lower bound of this integer type.
     */
    public IntervalBound getLower() {
        return this.lower;
    }

    /**
     * @return Number of representable values.
     */
    public BigInteger getNumberOfValues() {
        return this.numberOfValues;
    }

    /**
     * @return Upper bound of this integer type.
     */
    public IntervalBound getUpper() {
        return this.upper;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.lower == null) ? 0 : this.lower.hashCode());
        result = prime * result + ((this.upper == null) ? 0 : this.upper.hashCode());
        return result;
    }

    /**
     * @return Flag deciding if one bit is used to indicate the sign or not.
     */
    public boolean isBounded() {
        return this.lower.isFinite() && this.upper.isFinite();
    }

    /**
     * @return Flag deciding if one bit is used to indicate the sign or not.
     */
    public boolean isSigned() {
        return this.signed;
    }

    @Override
    public String toString() {
        if (this.signed) {
            return this.bitSize + "bits, signed";
        }
        return this.bitSize + "bits, unsigned";
    }

}
