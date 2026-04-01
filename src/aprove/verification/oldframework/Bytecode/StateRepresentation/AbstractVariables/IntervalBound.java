package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;

import immutables.*;

/**
 * Instances of this class are used as bounds in intervals, which are used for
 * abstract integers. Each bound either is a number or positive infinity or
 * negative infinity.
 * @author cotto
 */
public final class IntervalBound implements Immutable {
    /**
     * One!
     */
    public static final IntervalBound ONE = new IntervalBound(BigInteger.ONE);

    /**
     * Zero!
     */
    public static final IntervalBound ZERO = new IntervalBound(BigInteger.ZERO);

    /**
     * Minus one!
     */
    public static final IntervalBound NEGONE = new IntervalBound(BigInteger.ONE.negate());

    /**
     * Integer.MAX_VALUE
     */
    static final IntervalBound MAXINT = new IntervalBound(Integer.MAX_VALUE);

    /**
     * Integer.MIN_VALUE
     */
    static final IntervalBound MININT = new IntervalBound(Integer.MIN_VALUE);

    /**
     * Long.MAX_VALUE
     */
    static final IntervalBound MAXLONG = new IntervalBound(Long.MAX_VALUE);

    /**
     * Long.MIN_VALUE
     */
    static final IntervalBound MINLONG = new IntervalBound(Long.MIN_VALUE);

    /**
     * Positive infinity.
     */
    static final IntervalBound POSINF = new IntervalBound(true);

    /**
     * Negative infinity.
     */
    static final IntervalBound NEGINF = new IntervalBound(false);

    /**
     * If non-null, this bound is just some literal. If null, it is -inf or
     * +inf, see {@link IntervalBound#posInf}
     */
    private final BigInteger constant;

    /**
     * If {@link IntervalBound#constant} is null, this bound is +inf iff this
     * field is true, otherwise it is -inf.
     */
    private final boolean posInf;

    /**
     * Create a new IntervalBound which is -inf or +inf
     * @param isPosInf iff true, this is +inf, otherwise -inf
     */
    private IntervalBound(final boolean isPosInf) {
        this.constant = null;
        this.posInf = isPosInf;
    }

    /**
     * Create a new IntervalBound which is just some number.
     * @param cons the number
     */
    private IntervalBound(final BigInteger cons) {
        this.constant = cons;
        this.posInf = false;
    }

    /**
     * Create a new IntervalBound which is just some number.
     * @param i the number
     */
    private IntervalBound(final long i) {
        this(BigInteger.valueOf(i));
    }

    /**
     * @param num some number
     * @return an IntervalBound instance for the given number
     */
    public static IntervalBound create(final BigInteger num) {
        if (IntervalBound.ZERO.constant.equals(num)) {
            return IntervalBound.ZERO;
        }
        if (IntervalBound.ONE.constant.equals(num)) {
            return IntervalBound.ONE;
        }
        if (IntervalBound.NEGONE.constant.equals(num)) {
            return IntervalBound.NEGONE;
        }
        return new IntervalBound(num);
    }

    /**
     * @return an IntervalBound with the absolute value of this
     */
    public IntervalBound abs() {
        if (this.constant == null) {
            return IntervalBound.POSINF;
        }
        if (this.constant.signum() >= 0) {
            return this;
        }
        return IntervalBound.create(this.constant.abs());
    }

    /**
     * @param summand the summand
     * @return an IntervalBound which is the result of adding the argument to
     * this
     */
    public IntervalBound add(final IntervalBound summand) {
        if (this.constant == null) {
            if (summand.constant == null) {
                assert (this.posInf == summand.posInf);
            }
            return this;
        }
        if (summand.constant == null) {
            return summand;
        }
        return IntervalBound.create(this.constant.add(summand.constant));
    }

    /**
     * @param arg the number to compare with
     * @return -1, 0, 1 if this number is smaller / equal / bigger than the
     * argument
     */
    public int compareTo(final BigInteger arg) {
        if (this.constant == null) {
            if (this.posInf) {
                return 1;
            }
            return -1;
        }
        return this.constant.compareTo(arg);
    }

    /**
     * Do not compare two infinites of the same sign! WTF??? GU!!! infinties are considered equal
     * @param arg the number to compare with
     * @return -1, 0, 1 if this number is smaller / equal / bigger than the
     * argument
     */
    public int compareTo(final IntervalBound arg) {
        if (arg.constant != null) {
            return this.compareTo(arg.constant);
        }
        if (this.constant != null) {
            if (arg.posInf) {
                return -1;
            }
            return 1;
        }
        if (this.posInf == arg.posInf) {
            return 0;
        }
        if (this.posInf) {
            return 1;
        }
        return -1;
    }

    /**
     * @param divisor the divisor
     * @return this divided by the divisor
     */
    public IntervalBound divide(final IntervalBound divisor) {
        if (this.constant != null && divisor.constant != null) {
            return IntervalBound.create(this.constant.divide(divisor.constant));
        }
        if (this.constant != null) {
            return IntervalBound.ZERO;
        }
        if (divisor.constant != null) {
            assert (!divisor.isZero());
            if (this.signum() == divisor.signum()) {
                return IntervalBound.POSINF;
            }
            return IntervalBound.NEGINF;
        }
        assert (false);
        return null;
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
        final IntervalBound other = (IntervalBound) obj;
        if (this.constant == null) {
            if (other.constant != null) {
                return false;
            }
        } else if (!this.constant.equals(other.constant)) {
            return false;
        }
        if (this.posInf != other.posInf) {
            return false;
        }
        return true;
    }

    /**
     * @return the BigInteger constant of this bound
     */
    public BigInteger getConstant() {
        assert (this.constant != null);
        return this.constant;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.constant == null) ? 0 : this.constant.hashCode());
        result = prime * result + (this.posInf ? 1231 : 1237);
        return result;
    }

    /**
     * @return true iff this bound is not +/- inf
     */
    public boolean isFinite() {
        return this.constant != null;
    }

    /**
     * @return true iff this bound is negative
     */
    public boolean isNegative() {
        return this.signum() < 0;
    }

    /**
     * @return false iff this bound is >= 0
     */
    public boolean isNonNegative() {
        return this.signum() >= 0;
    }

    /**
     * @return false iff this bound is <= 0
     */
    public boolean isNonPositive() {
        return this.signum() <= 0;
    }

    /**
     * @return true iff this bound is positive
     */
    public boolean isPositive() {
        return this.signum() > 0;
    }

    /**
     * @return true iff this bound is 0
     */
    public boolean isZero() {
        return this.equals(IntervalBound.ZERO);
    }

    /**
     * @param isLong whether we want to know something about Integer- or Long-values
     * @return whether this bound equals the highest or lowest valid value (which is POSINF or NEGINF if we ignore
     *  integer-bounds)
     */
    public boolean isAtBound(final boolean isLong) {
        return !this.isFinite() || (!isLong && (this.equals(IntervalBound.MININT) || this.equals(IntervalBound.MAXINT)))
            || (isLong && (this.equals(IntervalBound.MINLONG) || this.equals(IntervalBound.MAXLONG)));
    }

    /**
     * @param arg some bound
     * @return the bigger of the two bounds
     */
    public IntervalBound max(final IntervalBound arg) {
        if (this.constant == null) {
            if (this.posInf) {
                return IntervalBound.POSINF;
            }
            return arg;
        }
        if (arg.constant == null) {
            if (arg.posInf) {
                return IntervalBound.POSINF;
            }
            return this;
        }
        return IntervalBound.create(this.constant.max(arg.constant));
    }

    /**
     * @param arg some bound
     * @return the lower of the two bounds
     */
    public IntervalBound min(final IntervalBound arg) {
        if (this.constant == null) {
            if (!this.posInf) {
                return IntervalBound.NEGINF;
            }
            return arg;
        }
        if (arg.constant == null) {
            if (!arg.posInf) {
                return IntervalBound.NEGINF;
            }
            return this;
        }
        return IntervalBound.create(this.constant.min(arg.constant));
    }

    /**
     * 0 * inf is not defined.
     * @param factor the factor
     * @return an IntervalBound which is the result of multiplying the factor to
     * this.
     */
    public IntervalBound mul(final IntervalBound factor) {
        if (this.constant != null && factor.constant != null) {
            return IntervalBound.create(this.constant.multiply(factor.constant));
        }
        if (this.constant == null) {
            // 0 * inf is defined to be 0, because inf is just some arbitrary number
            if (factor.isZero()) {
                return factor;
            }
            final boolean negThis = this.isNegative();
            final boolean negThat = factor.isNegative();
            final boolean resultNeg = (negThis && !negThat) || (!negThis && negThat);
            if (resultNeg) {
                return IntervalBound.NEGINF;
            }
            return IntervalBound.POSINF;
        }
        return factor.mul(this);
    }

    /**
     * @return the negation of this bound
     */
    public IntervalBound negate() {
        if (this.constant == null) {
            if (this.posInf) {
                return IntervalBound.NEGINF;
            }
            return IntervalBound.POSINF;
        }
        return IntervalBound.create(this.constant.negate());
    }

    /**
     * @return -1, 0, 1 for negative value, 0, positive value.
     */
    public int signum() {
        if (this.constant != null) {
            return this.constant.signum();
        }
        if (this.posInf) {
            return 1;
        }
        return -1;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        if (this.equals(IntervalBound.MAXINT)) {
            return "MAXINT";
        }
        if (this.equals(IntervalBound.MININT)) {
            return "MININT";
        }
        if (this.equals(IntervalBound.MAXLONG)) {
            return "MAXLONG";
        }
        if (this.equals(IntervalBound.MINLONG)) {
            return "MINLONG";
        }
        if (this.constant != null) {
            return this.constant.toString();
        }
        if (this.posInf) {
            return "+inf";
        }
        return "-inf";
    }

    /**
     * oposite of {@code IntervalBound#toString()}
     * @param text String-representation of an IntervalBound
     * @return IntervalBound represented by the given String
     */
    public static IntervalBound parse(final String text) {
        if ("+inf".equals(text)) {
            return IntervalBound.POSINF;
        } else if ("-inf".equals(text)) {
            return IntervalBound.NEGINF;
        } else {
            return IntervalBound.create(new BigInteger(text));
        }
    }
}
