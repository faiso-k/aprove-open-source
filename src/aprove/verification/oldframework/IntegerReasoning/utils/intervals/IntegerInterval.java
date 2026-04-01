package aprove.verification.oldframework.IntegerReasoning.utils.intervals;

import java.math.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * Adapted from {@link IntervalInt}
 *
 * @author Alexander Weinert
 */
public class IntegerInterval {
    private final IntervalBound lowerBound;
    private final IntervalBound upperBound;

    /**
     * @param literal Some literal. Must not be null.
     * @return An interval containing only the given literal
     */
    public static IntegerInterval createLiteral(final BigInteger literal) {
        final IntervalBound bound = IntervalBound.create(literal);
        return new IntegerInterval(bound, bound);
    }

    /**
     * @param lowerBound Some lower bound. Null is interpreted as -inf
     * @param upperBound Some upper bound. Null is interpreted as +inf
     * @return An interval containing the integers between lowerBound and upperBound
     */
    public static IntegerInterval create(final BigInteger lowerBound, final BigInteger upperBound) {
        IntervalBound low = null;
        if (lowerBound == null) {
            low = IntervalBound.NEGINF;
        } else {
            low = IntervalBound.create(lowerBound);
        }

        IntervalBound up = null;
        if (upperBound == null) {
            up = IntervalBound.POSINF;
        } else {
            up = IntervalBound.create(upperBound);
        }

        return new IntegerInterval(low, up);
    }

    private IntegerInterval(final IntervalBound lowerBound, final IntervalBound upperBound) {
        assert !lowerBound.equals(IntervalBound.POSINF);
        assert !upperBound.equals(IntervalBound.NEGINF);
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
    }

    public boolean canInferEquals(final IntegerInterval other) {
        if (this.isLiteral() && other.isLiteral()) {
            return this.getLiteral().equals(other.getLiteral());
        } else {
            return false;
        }
    }

    public boolean canInferUnequals(final IntegerInterval other) {
        if (this.upperBound.equals(IntervalBound.POSINF) && other.upperBound.equals(IntervalBound.POSINF)) {
            return false;
        }
        if (this.lowerBound.equals(IntervalBound.NEGINF) && other.lowerBound.equals(IntervalBound.NEGINF)) {
            return false;
        }

        if (this.upperBound.compareTo(other.lowerBound) < 0) {
            return true;
        }
        if (this.lowerBound.compareTo(other.upperBound) > 0) {
            return true;
        }

        return false;
    }

    public boolean canInferLessThan(final IntegerInterval other) {
        if (this.upperBound.isFinite()) {
            return this.upperBound.compareTo(other.lowerBound) < 0;
        } else {
            return false;
        }
    }

    public boolean canInferLessThanEquals(final IntegerInterval other) {
        if (this.upperBound.isFinite()) {
            return this.upperBound.compareTo(other.lowerBound) <= 0;
        } else {
            return false;
        }
    }

    public IntegerInterval add(final IntegerInterval other) {
        if (other.isZero()) {
            return this;
        }

        final IntervalBound newLow = this.lowerBound.add(other.lowerBound);
        final IntervalBound newUp = this.upperBound.add(other.upperBound);

        return new IntegerInterval(newLow, newUp);
    }

    public IntegerInterval subtract(final IntegerInterval other) {
        if (other.isZero()) {
            return this;
        }

        final IntervalBound newLow;
        if (this.lowerBound.equals(IntervalBound.NEGINF)) {
            newLow = IntervalBound.NEGINF;
        } else if (other.upperBound.equals(IntervalBound.POSINF)) {
            newLow = IntervalBound.NEGINF;
        } else {
            newLow = this.lowerBound.subtract(other.upperBound);
        }

        final IntervalBound newUp;
        if (this.upperBound.equals(IntervalBound.POSINF)) {
            newUp = IntervalBound.POSINF;
        } else if (other.lowerBound.equals(IntervalBound.NEGINF)) {
            newUp = IntervalBound.POSINF;
        } else {
            newUp = this.upperBound.subtract(other.lowerBound);
        }

        return new IntegerInterval(newLow, newUp);
    }

    public IntegerInterval negate() {
        final IntervalBound newLow = this.upperBound.negate();
        final IntervalBound newUp = this.lowerBound.negate();

        return new IntegerInterval(newLow, newUp);
    }

    public IntegerInterval multiply(final IntegerInterval other) {
        if (other.isOne()) {
            return this;
        }
        if (other.isZero()) {
            return other;
        }
        if (other.isNegOne()) {
            return this.negate();
        }

        //[a,b] * [c,d] = [min{ac,ad,bc,bd}, max{ac,ad,bc,bd}]

        final IntervalBound ac = this.lowerBound.mul(other.lowerBound);
        final IntervalBound ad = this.lowerBound.mul(other.upperBound);
        final IntervalBound bc = this.upperBound.mul(other.lowerBound);
        final IntervalBound bd = this.upperBound.mul(other.upperBound);

        final IntervalBound lowerBound = ac.min(ad).min(bc).min(bd);
        final IntervalBound upperBound = ac.max(ad).max(bc).max(bd);

        final IntegerInterval res = new IntegerInterval(lowerBound, upperBound);

        return res;

    }

    /**
     * @return True if there is some BigInteger that is the only value in this
     * interval
     */
    private boolean isLiteral() {
        return this.lowerBound.isFinite() && this.lowerBound.equals(this.upperBound);
    }

    /**
     * @return If this interval contains only a single number, returns that
     * number. Null otherwise.
     */
    private BigInteger getLiteral() {
        if (this.isLiteral()) {
            return this.lowerBound.getConstant();
        } else {
            return null;
        }
    }

    /**
     * @param literal Some BigInteger
     * @return True if this interval only contains the given literal
     */
    private boolean isLiteral(final BigInteger literal) {
        final IntervalBound literalBound = IntervalBound.create(literal);
        final boolean lowerBoundIsLiteral = this.lowerBound.isFinite() && this.lowerBound.equals(literalBound);
        final boolean upperBoundIsLiteral = this.upperBound.isFinite() && this.upperBound.equals(literalBound);
        return lowerBoundIsLiteral && upperBoundIsLiteral;
    }

    /**
     * @return True if this interval only contains 0
     */
    private boolean isZero() {
        return this.isLiteral(BigInteger.ZERO);
    }

    /**
     * @return True if this interval only contains 1
     */
    private boolean isOne() {
        return this.isLiteral(BigInteger.ONE);
    }

    /**
     * @return True if this interval only contains -1
     */
    private boolean isNegOne() {
        return this.isLiteral(BigInteger.valueOf(-1));
    }

    @Override
    public String toString() {
        final StringBuilder stringBuilder = new StringBuilder();
        if (this.lowerBound.isFinite()) {
            stringBuilder.append("[");
        } else {
            stringBuilder.append("(");
        }
        stringBuilder.append(this.lowerBound.toString());
        stringBuilder.append(";");
        stringBuilder.append(this.upperBound.toString());
        if (this.upperBound.isFinite()) {
            stringBuilder.append("]");
        } else {
            stringBuilder.append(")");
        }
        return stringBuilder.toString();
    }

    /**
     * @return A new IntegerInterval with the same upper bound as this one
     * and the lower bound set to -inf
     */
    public IntegerInterval removeLowerBound() {
        return new IntegerInterval(IntervalBound.NEGINF, this.upperBound);
    }

    /**
     * @return A new IntegerInterval with the same lower bound as this one
     * and the upper bound set to +inf
     */
    public IntegerInterval removeUpperBound() {
        return new IntegerInterval(this.lowerBound, IntervalBound.POSINF);
    }

    public IntegerInterval divideByLiteral(final BigInteger coefficient) {
        assert coefficient.compareTo(BigInteger.ZERO) != 0 : "Cannot divide by 0";

        if (coefficient.compareTo(BigInteger.ZERO) > 0) {
            final IntervalBound newLow = this.lowerBound.divide(IntervalBound.create(coefficient));
            final IntervalBound newUp = this.upperBound.divide(IntervalBound.create(coefficient));
            return new IntegerInterval(newLow, newUp);
        } else {
            return this.negate().divideByLiteral(coefficient.negate());
        }
    }

    /**
     * @param other Some IntegerInterval
     * @return true if this is a superset of other
     */
    public boolean contains(final IntegerInterval other) {
        if (this.upperBound.equals(IntervalBound.POSINF)) {
            // There is no problem at the upper bound, fall through to checking lower bound
        } else if (other.upperBound.equals(IntervalBound.POSINF)) {
            // Our upper bound does not equal POSINF, the other one does, so everything above
            // our upper bound is in the other interval, but not in this one
            return false;
        } else if (this.upperBound.compareTo(other.upperBound) < 0) {
            return false;
        }

        if (this.lowerBound.equals(IntervalBound.NEGINF)) {
            return true;
        } else if (other.lowerBound.equals(IntervalBound.NEGINF)) {
            return false;
        } else {
            return this.lowerBound.compareTo(other.lowerBound) <= 0;
        }
    }

    /**
     * @return True if this is the interval (-inf,+inf)
     */
    public boolean isUniversalInterval() {
        return this.upperBound.equals(IntervalBound.POSINF) && this.lowerBound.equals(IntervalBound.NEGINF);
    }

    public IntegerInterval intersect(final IntegerInterval other) {
        final IntervalBound newLower = this.lowerBound.max(other.lowerBound);
        final IntervalBound newUpper = this.upperBound.min(other.upperBound);
        return new IntegerInterval(newLower, newUpper);
    }

    public IntegerInterval merge(final IntegerInterval other) {
        final IntervalBound newLower = this.lowerBound.min(other.lowerBound);
        final IntervalBound newUpper = this.upperBound.max(other.upperBound);
        return new IntegerInterval(newLower, newUpper);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.lowerBound == null) ? 0 : this.lowerBound.hashCode());
        result = prime * result + ((this.upperBound == null) ? 0 : this.upperBound.hashCode());
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
        if (!(obj instanceof IntegerInterval)) {
            return false;
        }
        final IntegerInterval other = (IntegerInterval) obj;
        if (this.lowerBound == null) {
            if (other.lowerBound != null) {
                return false;
            }
        } else if (!this.lowerBound.equals(other.lowerBound)) {
            return false;
        }
        if (this.upperBound == null) {
            if (other.upperBound != null) {
                return false;
            }
        } else if (!this.upperBound.equals(other.upperBound)) {
            return false;
        }
        return true;
    }

    public BigInteger getUpperBoundIfFinite() {
        return this.upperBound.isFinite() ? this.upperBound.getConstant() : null;
    }

    public BigInteger getLowerBoundIfFinite() {
        return this.lowerBound.isFinite() ? this.lowerBound.getConstant() : null;
    }

    public IntegerInterval multiplyByLiteral(final BigInteger literal) {
        final IntervalBound newUp, newLow;

        final int literalCompareToZero = literal.compareTo(BigInteger.ZERO);
        if (literalCompareToZero == 0) {
            newLow = IntervalBound.create(BigInteger.ZERO);
            newUp = IntervalBound.create(BigInteger.ZERO);
        } else if (literalCompareToZero > 0) {
            if (this.upperBound.equals(IntervalBound.POSINF)) {
                newUp = IntervalBound.POSINF;
            } else {
                newUp = IntervalBound.create(this.upperBound.getConstant().multiply(literal));
            }

            if (this.lowerBound.equals(IntervalBound.NEGINF)) {
                newLow = IntervalBound.NEGINF;
            } else {
                newLow = IntervalBound.create(this.lowerBound.getConstant().multiply(literal));
            }
        } else {
            // literalCompareToZero < 0
            if (this.upperBound.equals(IntervalBound.POSINF)) {
                newLow = IntervalBound.NEGINF;
            } else {
                newLow = IntervalBound.create(this.upperBound.getConstant().multiply(literal));
            }

            if (this.lowerBound.equals(IntervalBound.NEGINF)) {
                newUp = IntervalBound.POSINF;
            } else {
                newUp = IntervalBound.create(this.lowerBound.getConstant().multiply(literal));
            }
        }

        return new IntegerInterval(newLow, newUp);
    }

    /**
     * @return True if all values in this interval are <= 0. False otherwise.
     */
    public boolean isNonPositive() {
        return this.upperBound.compareTo(BigInteger.ZERO) <= 0;
    }

    /**
     * @return True if all values in this interval are >= 0. False otherwise.
     */
    public boolean isNonNegative() {
        return this.lowerBound.compareTo(BigInteger.ZERO) >= 0;
    }

    /**
     * @return True if all values in this interval are > 0. False otherwise.
     */
    public boolean isPositive() {
        return this.lowerBound.compareTo(BigInteger.ZERO) > 0;
    }

    /**
     * @return True if all values in this interval are > 1. False otherwise.
     */
    public boolean isBiggerOne() {
        return this.lowerBound.compareTo(BigInteger.ONE) > 0;
    }

    /**
     * @return True if all values in this interval are < 0. False otherwise.
     */
    public boolean isNegative() {
        return this.upperBound.compareTo(BigInteger.ZERO) < 0;
    }

    /**
     * @return True if all values in this interval are < -1. False otherwise.
     */
    public boolean isSmallerMinusOne() {
        return this.upperBound.compareTo(BigInteger.valueOf(-1)) < 0;
    }

}
