package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of int/long values realized by storing an interval [x, y] of
 * represented values. [-inf, +inf] is used to represent all values.
 * <p>
 * The additional information !=0 can be used to represent ranges where 0 is
 * excluded, e.g. [-5, 5]\{0}. The IntervalBoundedInt [0, 5]\{0} is not valid.
 * @author Carsten Otto, Marc Brockschmidt, Jera Hensel
 */
public final class IntervalBoundedInt extends AbstractBoundedInt {

    /**
     * The string used to denote that the interval does not contain zero.
     */
    private static final String NO_ZERO = "\\{0}";

    /**
     * True iff 0 is represented (set to false to build a special case like
     * [-5, +5] \ {0}). This may only be set if the interval defined by the
     * lower and upper bounds includes zero. It may not be unset if the interval
     * contains zero, but exactly one of the bounds is zero (e.g. [0, 5]\{0}
     * must be implemented as [1,5] instead).
     */
    private final boolean containsZero;

    /**
     * The lower part of the interval.
     */
    private final IntervalBound lower;

    /**
     * This counter tells how often the interval was widened towards the lower
     * bound during abstraction.
     */
    private final int lowerCounter;

    /**
     * The maximal upper bound that was used for this interval.
     */
    private final IntervalBound maximalUpperBound;

    /**
     * The minimal lower bound that was used for this interval.
     */
    private final IntervalBound minimalLowerBound;

    /**
     * The upper part of the interval.
     */
    private final IntervalBound upper;

    /**
     * This counter tells how often the interval was widened towards the upper
     * bound during abstraction.
     */
    private final int upperCounter;

    /**
     * Create an unknown integer.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     */
    IntervalBoundedInt(final IntegerType intType) {
        this.lower = intType.getLower();
        this.minimalLowerBound = intType.getLower();
        this.upper = intType.getUpper();
        this.maximalUpperBound = intType.getUpper();
        this.lowerCounter = 0;
        this.upperCounter = 0;
        this.containsZero = true;
    }

    /**
     * Create a new {@link IntervalBoundedInt} based on the two interval bounds.
     * @param low the lower bound of the interval
     * @param up the upper bound of the interval
     * @param containsZeroParam true iff the abstract integer also represents
     * zero
     * @param minLow the minimal lower bound used for this interval in its arithmetic history.
     *  If <code>low</code> is smaller, it is used instead.
     * @param maxUp the maximal upper bound used for this interval in its arithmetic history
     *  If <code>up</code> is bigger, it is used instead.
     * @param newLowerCounter how often the interval was widened towards the
     * lower bound during abstraction.
     * @param newUpperCounter how often the interval was widened towards the
     * upper bound during abstraction.
     */
    IntervalBoundedInt(
        final IntervalBound low,
        final IntervalBound up,
        final boolean containsZeroParam,
        final IntervalBound minLow,
        final IntervalBound maxUp,
        final int newLowerCounter,
        final int newUpperCounter)
    {
        assert (low.compareTo(up) < 0);
        this.lower = low;
        this.upper = up;
        this.minimalLowerBound = low.min(minLow);
        this.maximalUpperBound = up.max(maxUp);
        this.lowerCounter = newLowerCounter;
        this.upperCounter = newUpperCounter;
        this.containsZero = containsZeroParam;
        if (Globals.useAssertions) {
            if (containsZeroParam) {
                assert (IntervalBoundedInt.containsZero(low, up));
            } else {
                // [0, x] and [0, y] are not okay
                assert (!low.isZero() && !up.isZero());
            }
        }
    }

    /**
     * @param low the lower bound of the interval
     * @param up the upper bound of the interval
     * @return true iff the interval given by low and up includes 0.
     */
    static boolean containsZero(final IntervalBound low, final IntervalBound up) {
        return (low.signum() <= 0) && (up.signum() >= 0);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractBoundedInt absolute(final IntegerType intType) throws OverflowException {
        if (this.isNonNegative()) {
            return this;
        }
        IntervalBound low = IntervalBound.ZERO;
        if (!this.containsZero) {
            low = IntervalBound.ONE;
        }
        if (this.upper.isNegative()) {
            low = this.upper.abs();
        }
        final IntervalBound up = this.upper.max(this.lower.abs());
        final AbstractBoundedInt res =
            AbstractBoundedInt.create(
                low,
                up,
                this.containsZero,
                this.minimalLowerBound,
                this.maximalUpperBound,
                this.lowerCounter,
                this.upperCounter);

        if (!intType.canRepresent(res)) {
            throw new OverflowException(intType, ArithmeticOperationType.NEG, res);
        }

        return res;
    }

    /** {@inheritDoc} */
    @Override
    public Triple<AbstractBoundedInt, BigInteger, BigInteger> add(
        final AbstractBoundedInt n,
        final IntegerType intType,
        final boolean handleOverflows,
        final YNM posOverflow,
        final YNM negOverflow
    ) throws OverflowException {
        if (n.isZero()) {
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(this, null, null);
        }

        AbstractBoundedInt res = this;

        final int newLowerCounter = Math.max(this.lowerCounter, n.getLowerCounter());
        final int newUpperCounter = Math.max(this.upperCounter, n.getUpperCounter());

        final IntervalBound newLow = this.lower.add(n.getLower());
        final IntervalBound newUp = this.upper.add(n.getUpper());
        final boolean newContainsZero = IntervalBoundedInt.containsZero(newLow, newUp);

        if (!newLow.equals(this.lower) || !newUp.equals(this.upper) || newContainsZero != this.containsZero) {
            if (intType.isBounded()) {
                res =
                    AbstractBoundedInt.create(
                        newLow,
                        newUp,
                        newContainsZero,
                        intType.getLower(),
                        intType.getUpper(),
                        newLowerCounter,
                        newUpperCounter);
            } else {
                res =
                    AbstractBoundedInt.create(
                        newLow,
                        newUp,
                        newContainsZero,
                        this.minimalLowerBound.min(n.getMinLower()),
                        this.maximalUpperBound.max(n.getMaxUpper()),
                        newLowerCounter,
                        newUpperCounter);
            }
            if (n.isLiteral()) {
                res.copyComparisonsFrom(this);
            }
        }

        if (!intType.canRepresent(res)) {
            if (!handleOverflows) {
                throw new OverflowException(intType, ArithmeticOperationType.ADD, res);
            } else {
                Triple<AbstractBoundedInt, BigInteger, BigInteger> result =
                    res.adjustToBounds(intType, posOverflow, negOverflow);
                return result;
            }
        }

        return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(res, null, null);
    }

    /** {@inheritDoc} */
    @Override
    public Triple<AbstractBoundedInt, BigInteger, BigInteger> adjustToBounds(
        final IntegerType intType,
        final YNM posOverflow,
        final YNM negOverflow
    ) {
        AbstractBoundedInt res = null;
        if (Globals.useAssertions) {
            assert (this.lower.compareTo(this.upper) < 0);
        }
        BigInteger adjustedLow = this.lower.getConstant();
        BigInteger adjustedUp = this.upper.getConstant();
        BigInteger size = BigInteger.valueOf(2).pow(intType.getBitSize());

        if (this.upper.getConstant().subtract(this.lower.getConstant()).compareTo(size) >= 0) {
            // The range of values is bigger than the size of the type, so return the whole interval.
            res =
                AbstractBoundedInt.create(
                    intType.getLower(),
                    intType.getUpper(),
                    true,
                    intType.getLower(),
                    intType.getUpper(),
                    this.lowerCounter,
                    this.upperCounter);
        } else {
            // The range of values is smaller than the size of the type.

            boolean found = false;

            if (adjustedUp.compareTo(intType.getUpper().getConstant()) > 0) {
                // The upper bound exceeds its type bounds.
                if (posOverflow == YNM.NO) {
                    // If we can exclude an overflow, we just choose the maximum value as upper bound.
                    adjustedUp = intType.getUpper().getConstant();
                    found = true;
                } else if (
                    posOverflow == YNM.YES && adjustedLow.compareTo(intType.getUpper().getConstant()) <= 0
                ) {
                    // If we have an overflow for sure, and the lower bound does not exceed the type bounds, we choose
                    // the minimum value as lower bound and adjust the upper bound into its range.
                    adjustedLow = intType.getLower().getConstant();
                    adjustedUp = adjustedUp.subtract(size);
                    found = true;
                }
            }

            if (adjustedLow.compareTo(intType.getLower().getConstant()) < 0) {
                // The lower bound is below its type bound.
                if (negOverflow == YNM.NO) {
                    // If we can exclude an overflow, we just choose the minimum value as lower bound.
                    adjustedLow = intType.getLower().getConstant();
                    found = true;
                } else if (negOverflow == YNM.YES && adjustedUp.compareTo(intType.getLower().getConstant()) >= 0){
                    // If we have an overflow for sure, and the upper bound is not below the type bounds, we choose
                    // the maximum value as upper bound and adjust the lower bound into its range.
                    adjustedUp = intType.getUpper().getConstant();
                    adjustedLow = adjustedLow.add(size);
                    found = true;
                }
            }

            if (!found){
                // If the upper bound is above the valid range, lower the whole interval until the upper bound reaches
                // a valid value.
                while (adjustedUp.compareTo(intType.getUpper().getConstant()) > 0) {
                    adjustedUp = adjustedUp.subtract(size);
                    adjustedLow = adjustedLow.subtract(size);
                }

                // If the lower bound is below the valid range, raise it until it reaches a valid value.
                while (adjustedLow.compareTo(intType.getLower().getConstant()) < 0) {
                    if (adjustedUp.compareTo(intType.getLower().getConstant()) < 0){
                        adjustedUp = adjustedUp.add(size);
                    }
                    adjustedLow = adjustedLow.add(size);
                }
            }

            if (adjustedLow.compareTo(adjustedUp) <= 0) {
                // Lower bound <= upper bound, we have a valid new interval.
                res =
                    AbstractBoundedInt.create(
                        IntervalBound.create(adjustedLow),
                        IntervalBound.create(adjustedUp),
                        intType.getLower(),
                        intType.getUpper(),
                        this.lowerCounter,
                        this.upperCounter);
            } else {
                // Upper bound < lower bound. The new interval is the maximal interval.
                res =
                    AbstractBoundedInt.create(
                        intType.getLower(),
                        intType.getUpper(),
                        intType.getLower(),
                        intType.getUpper(),
                        this.lowerCounter,
                        this.upperCounter);

                // Return the bounds within the interval so that we do not lose any information.
                // Relations may be created afterwards.
                return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(res, adjustedUp, adjustedLow);
            }
        }

        return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(res, null, null);
    }

    /** {@inheritDoc} */
    @Override
    public AbstractBoundedInt and(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean ignoreOverflows)
    {
        if (sameReference) {
            return this;
        }

        // If n is a literal, let's first lower the upper bound of this interval
        IntervalBound atMost = this.isNonNegative() ? this.getUpper() : intType.getUpper();
        if (n.isIntLiteral() && intType.isBounded() && intType.getBitSize() > 1) {
            final BigInteger absOfN = n.getIntLiteralValue().abs();
            BigInteger newUpper = atMost.getConstant();
            // If the absolute value of n is a power of 2, the last log(abs(n)) bits of n (and hence the result) are 0
            int i = absOfN.getLowestSetBit() - 1;
            while (i >= 0) {
                BigInteger shiftedOne = BigInteger.ONE.shiftLeft(i);
                newUpper = newUpper.andNot(shiftedOne);
                i--;
            }
            atMost = IntervalBound.create(newUpper);
        }

        final int newLowerCounter = Math.max(this.lowerCounter, n.getLowerCounter());
        final int newUpperCounter = Math.max(this.upperCounter, n.getUpperCounter());

        final IntervalBound minLower = ignoreOverflows ? IntegerType.UNBOUND.getLower() : intType.getLower();

        /*
         * The first bit represents the sign. neg & neg stays neg, everything
         * else becomes pos.
         */
        final AbstractBoundedInt res;
        if (this.isNegative() && n.isNegative()) {
            final IntervalBound minAB = this.upper.min(n.getUpper());
            res =
                AbstractBoundedInt.create(
                    minLower,
                    minAB,
                    false,
                    this.minimalLowerBound.min(n.getMinLower()),
                    this.maximalUpperBound.max(n.getMaxUpper()),
                    newLowerCounter,
                    newUpperCounter);
        } else if (this.isNonNegative() && n.isNonNegative()) {
            // BearPerson said this.
            final IntervalBound minAB = this.upper.min(n.getUpper()).min(atMost);
            res =
                AbstractBoundedInt.create(
                    IntervalBound.ZERO,
                    minAB,
                    true,
                    this.minimalLowerBound.min(n.getMinLower()),
                    this.maximalUpperBound.max(n.getMaxUpper()),
                    newLowerCounter,
                    newUpperCounter);
        } else if (this.isNonNegative() || n.isNonNegative()) {
            final IntervalBound newUpper = this.isNonNegative() ? this.upper.min(atMost) : n.getUpper().min(atMost);
            res =
                AbstractBoundedInt.create(
                    IntervalBound.ZERO,
                    newUpper,
                    true,
                    this.minimalLowerBound.min(n.getMinLower()),
                    this.maximalUpperBound.max(n.getMaxUpper()),
                    newLowerCounter,
                    newUpperCounter);
        } else {
            final IntervalBound maxAB = this.upper.max(n.getUpper()).min(atMost);
            res =
                AbstractBoundedInt.create(
                    minLower,
                    maxAB,
                    true,
                    this.minimalLowerBound.min(n.getMinLower()),
                    this.maximalUpperBound.max(n.getMaxUpper()),
                    newLowerCounter,
                    newUpperCounter);
        }

        assert (ignoreOverflows || intType.canRepresent(res)) : "AND implementation resulted in value not representable in integer type => Bug.";

        return res;
    }

    /** {@inheritDoc} */
    @Override
    public Integer compareToApprox(final AbstractBoundedInt n) {
        if (this.upper.compareTo(n.getLower()) < 0) {
            // [a, b] < [c, d] for b < c
            return -1;
        }
        if (this.lower.compareTo(n.getUpper()) > 0) {
            // [a, b] > [c, d] for a < d
            return 1;
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean containsInt(final AbstractBoundedInt other) {
        // Our lower bound should not be greater than the other's
        if ((this.lower.isFinite() || other.getLower().isFinite()) && this.lower.compareTo(other.getLower()) > 0) {
            return false;
        }
        // same for upper
        if ((this.upper.isFinite() || other.getUpper().isFinite()) && this.upper.compareTo(other.getUpper()) < 0) {
            return false;
        }
        // if we have the zero we don't care whether the other has
        if (this.containsZero) {
            return true;
        }
        return !other.containsLiteral(0);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean containsLiteral(final BigInteger i) {
        if (i.equals(BigInteger.ZERO)) {
            return this.containsZero;
        }
        if (this.lower.compareTo(i) <= 0) {
            return (this.upper.compareTo(i) >= 0);
        }
        return false;
    }

    /**
     * @param ref the reference pointing to <code>this</code>
     * @param label some label that is prepended to all variable names.
     * @return list of SMT atoms corresponding to the (finite) bounds of <code>this</code>.
     */
    public
        List<SMTLIBTheoryAtom>
        convertBoundsToSMTConstraints(final AbstractVariableReference ref, final String label)
    {
        final List<SMTLIBTheoryAtom> constraints = new LinkedList<>();
        final IntervalBound low = this.getLower();
        final IntervalBound up = this.getUpper();

        if (low.isFinite()) {
            constraints.add(SMTLIBIntLE.create(SMTLIBIntConstant.create(low.getConstant()), ref.toSMTIntValue(label)));
        }
        if (up.isFinite()) {
            constraints.add(SMTLIBIntLE.create(ref.toSMTIntValue(label), SMTLIBIntConstant.create(up.getConstant())));
        }
        return constraints;
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
        final IntervalBoundedInt other = (IntervalBoundedInt) obj;
        if (this.containsZero != other.containsZero) {
            return false;
        }
        if (this.lower == null) {
            if (other.lower != null) {
                return false;
            }
        } else if (!this.lower.equals(other.lower)) {
            return false;
        }
        if (this.lowerCounter != other.lowerCounter) {
            return false;
        }
        if (this.upper == null) {
            if (other.upper != null) {
                return false;
            }
        } else if (!this.upper.equals(other.upper)) {
            return false;
        }
        if (this.upperCounter != other.upperCounter) {
            return false;
        }
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equalsOnlyRepresentedValues(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final IntervalBoundedInt other = (IntervalBoundedInt) obj;
        if (this.containsZero != other.containsZero) {
            return false;
        }
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
     * {@inheritDoc}
     */
    @Override
    public BigInteger getLiteral() {
        assert (false);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IntervalBound getLower() {
        return this.lower;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getLowerCounter() {
        return this.lowerCounter;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IntervalBound getMaxUpper() {
        return this.maximalUpperBound;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IntervalBound getMinLower() {
        return this.minimalLowerBound;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractInt getThisAsAbstractInt() {
        return AbstractInt.create(
            this.lower,
            this.upper,
            this.containsZero,
            this.minimalLowerBound,
            this.maximalUpperBound,
            this.lowerCounter,
            this.upperCounter
        );
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IntervalBound getUpper() {
        return this.upper;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getUpperCounter() {
        return this.upperCounter;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.containsZero ? 1231 : 1237);
        result = prime * result + ((this.lower == null) ? 0 : this.lower.hashCode());
        result = prime * result + this.lowerCounter;
        result = prime * result + ((this.upper == null) ? 0 : this.upper.hashCode());
        result = prime * result + this.upperCounter;
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractBoundedInt intersect(final AbstractNumber other) throws IntersectionFailException {
        if (!(other instanceof AbstractBoundedInt)) {
            throw new IntersectionFailException("not an int: " + this.toString() + " " + other);
        }
        final AbstractBoundedInt otherInt = (AbstractBoundedInt) other;

        IntervalBound newLower = this.lower.max(otherInt.getLower());
        IntervalBound newUpper = this.upper.min(otherInt.getUpper());

        final boolean contains0 = this.containsZero && otherInt.containsLiteral(0);

        if (!contains0) {
            if (newLower.isZero()) {
                newLower = IntervalBound.create(BigInteger.ONE);
            }
            if (newUpper.isZero()) {
                newUpper = IntervalBound.create(BigInteger.ONE.negate());
            }
        }

        if (newLower.compareTo(newUpper) > 0) {
            throw new IntersectionFailException("empty intersection: " + this + " and " + other);
        }

        return AbstractBoundedInt.create(
            newLower,
            newUpper,
            contains0,
            newLower,
            newUpper,
            Math.max(this.lowerCounter, otherInt.getLowerCounter()),
            Math.max(this.upperCounter, otherInt.getUpperCounter()));
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractBoundedInt#isBiggerOne()
     */
    @Override
    public boolean isBiggerOne() {
        return this.lower.compareTo(BigInteger.ONE) > 0;
    }

    /** {@inheritDoc} */
    @Override
    public boolean isLiteral() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isNegative() {
        return this.upper.isNegative();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isNegOne() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isNonNegative() {
        return this.lower.isNonNegative();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isNonPositive() {
        return this.upper.isNonPositive();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isOne() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isPositive() {
        return this.lower.isPositive();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractBoundedInt#isSmallerMinusOne()
     */
    @Override
    public boolean isSmallerMinusOne() {
        return this.upper.compareTo(BigInteger.ONE.negate()) < 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isZero() {
        return false;
    }

    /** {@inheritDoc} */
    @Override
    public Triple<AbstractBoundedInt, BigInteger, BigInteger> mul(
        final AbstractBoundedInt n,
        final IntegerType intType,
        final boolean handleOverflows,
        final YNM posOverflow,
        final YNM negOverflow) throws OverflowException
    {
        if (n.isOne()) {
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(this, null, null);
        }
        if (n.isZero()) {
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(n, null, null);
        }
        if (n.isNegOne()) {
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(this.negate(intType), null, null);
        }

        final int newLowerCounter = Math.max(this.lowerCounter, n.getLowerCounter());
        final int newUpperCounter = Math.max(this.upperCounter, n.getUpperCounter());

        //[a,b] * [c,d] = [min{ac,ad,bc,bd}, max{ac,ad,bc,bd}]

        final IntervalBound ac = this.lower.mul(n.getLower());
        final IntervalBound ad = this.lower.mul(n.getUpper());
        final IntervalBound bc = this.upper.mul(n.getLower());
        final IntervalBound bd = this.upper.mul(n.getUpper());

        final boolean resWithZero = this.containsZero || n.containsLiteral(0);
        final IntervalBound lowerBound = ac.min(ad).min(bc).min(bd);
        final IntervalBound upperBound = ac.max(ad).max(bc).max(bd);

        AbstractBoundedInt res =
            AbstractBoundedInt.create(
                lowerBound,
                upperBound,
                resWithZero,
                this.minimalLowerBound.min(n.getMinLower()),
                this.maximalUpperBound.max(n.getMaxUpper()),
                newLowerCounter,
                newUpperCounter);
        if (n.isLiteral()) {
            res.copyComparisonsFrom(this);
        }

        if (!intType.canRepresent(res)) {
            if (!handleOverflows) {
                throw new OverflowException(intType, ArithmeticOperationType.MUL, res);
            } else {
                return res.adjustToBounds(intType, posOverflow, negOverflow);
            }
        }

        return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(res, null, null);
    }

    /** {@inheritDoc} */
    @Override
    public AbstractBoundedInt negate(final IntegerType intType) throws OverflowException {
        final IntervalBound newLow = this.upper.negate();
        final IntervalBound newUp = this.lower.negate();
        final boolean newContainsZero = this.containsZero && IntervalBoundedInt.containsZero(newLow, newUp);

        final AbstractBoundedInt res =
            AbstractBoundedInt.create(
                newLow,
                newUp,
                newContainsZero,
                this.minimalLowerBound,
                this.maximalUpperBound,
                this.lowerCounter,
                this.upperCounter);

        res.copyComparisonsFrom(this);

        if (!intType.canRepresent(res)) {
            throw new OverflowException(intType, ArithmeticOperationType.NEG, res);
        }

        return res;
    }

    /** {@inheritDoc} */
    @Override
    public AbstractBoundedInt or(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean ignoreOverflows)
    {
        if (sameReference) {
            return n;
        }

        final int newLowerCounter = Math.max(this.lowerCounter, n.getLowerCounter());
        final int newUpperCounter = Math.max(this.upperCounter, n.getUpperCounter());

        final IntervalBound minLower = ignoreOverflows ? IntegerType.UNBOUND.getLower() : intType.getLower();
        IntervalBound maxUpper = IntegerType.UNBOUND.getUpper();
        if (!ignoreOverflows && this.isNonNegative() && n.isNonNegative()) {
            BigInteger max = BigInteger.ONE;
            while (max.compareTo(this.getUpper().getConstant()) <= 0 || max.compareTo(n.getUpper().getConstant()) <= 0) {
                max = max.multiply(BigInteger.valueOf(2));
            }
            max = max.subtract(BigInteger.ONE);
            maxUpper = IntervalBound.create(max).min(intType.getUpper());
        }

        /*
         * The first bit represents the sign. pos | pos stays pos, everything
         * else becomes neg.
         */
        if (this.isNonNegative() && n.isNonNegative()) {
            // BearPerson said this.
            final IntervalBound maxAB = this.lower.max(n.getLower());
            return AbstractBoundedInt.create(
                maxAB,
                maxUpper,
                this.minimalLowerBound.min(n.getMinLower()),
                this.maximalUpperBound.max(n.getMaxUpper()),
                newLowerCounter,
                newUpperCounter);
        }

        final AbstractBoundedInt res =
            AbstractBoundedInt.create(
                minLower,
                IntervalBound.NEGONE,
                this.minimalLowerBound.min(n.getMinLower()),
                this.maximalUpperBound.max(n.getMaxUpper()),
                newLowerCounter,
                newUpperCounter);

        assert (ignoreOverflows || intType.canRepresent(res)) : "OR implementation resulted in value not representable in integer type => Bug.";

        return res;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractBoundedInt removeZeroFromInteger() {
        if (!this.containsZero) {
            return this;
        }
        IntervalBound newLow = this.lower;
        if (this.lower.isZero()) {
            newLow = IntervalBound.ONE;
        }
        IntervalBound newUp = this.upper;
        if (this.upper.isZero()) {
            newUp = IntervalBound.NEGONE;
        }
        return AbstractBoundedInt.create(
            newLow,
            newUp,
            false,
            this.minimalLowerBound,
            this.maximalUpperBound,
            this.lowerCounter,
            this.upperCounter);
    }

    /** {@inheritDoc} */
    @Override
    public AbstractBoundedInt shl(final AbstractBoundedInt n, final IntegerType intType, final boolean ignoreOverflows) {
        if (n.isLiteral()) {
            final BigInteger literalValue = n.getLiteral();
            final int lowerBits;
            if (intType.getBitSize() == 64) {
                lowerBits = literalValue.intValue() & 0x3f;
            } else {
                lowerBits = literalValue.intValue() & 0x1f;
            }
            if (lowerBits == 0) {
                return this;
            }
            IntervalBound newLow;
            if (this.getLower().isFinite()) {
                newLow = IntervalBound.create(this.getLower().getConstant().shiftLeft(lowerBits));
            } else {
                newLow = this.getLower();
            }
            IntervalBound newUp;
            if (this.getUpper().isFinite()) {
                newUp = IntervalBound.create(this.getUpper().getConstant().shiftLeft(lowerBits));
            } else {
                newUp = this.getUpper();
            }
            if (!ignoreOverflows) {
                newLow = intType.getLower().max(newLow);
                newUp = intType.getUpper().min(newUp);
            }
            /* This exception is not thrown on the basis of "if you use bit operations, you expect bit-level
             *  overflows":
                final AbstractBoundedInt res =
                    AbstractBoundedInt.create(newLow, newUp, this.isLongValue(), this.minimalLowerBound,
                        this.maximalUpperBound, this.lowerCounter, this.upperCounter);
                if (!intType.canRepresent(res)) {
                    throw new OverflowException(intType, IntArithType.SHL, res);
                }
             */
            final AbstractBoundedInt res =
                AbstractBoundedInt.create(
                    newLow,
                    newUp,
                    this.minimalLowerBound,
                    this.maximalUpperBound,
                    this.lowerCounter,
                    this.upperCounter);
            return res;
        }
        if (ignoreOverflows) {
            return AbstractBoundedInt.getUnknown(IntegerType.UNBOUND);
        } else {
            return AbstractBoundedInt.getUnknown(intType);
        }
    }

    /** {@inheritDoc} */
    @Override
    public AbstractBoundedInt shr(final AbstractBoundedInt n, final IntegerType intType, final boolean ignoreOverflows) {
        if (n.isLiteral()) {
            final BigInteger literalValue = n.getLiteral();

            final int lowerBits;
            if (intType.getBitSize() == 64) {
                lowerBits = literalValue.intValue() & 0x3f;
            } else {
                lowerBits = literalValue.intValue() & 0x1f;
            }
            if (lowerBits == 0) {
                return this;
            }
        }

        if (ignoreOverflows) {
            return AbstractBoundedInt.getUnknown(IntegerType.UNBOUND);
        } else {
            return AbstractBoundedInt.getUnknown(intType);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractBoundedInt toByteValue() throws OverflowException {
        return this.cast(IntegerType.I8);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractBoundedInt toCharValue() throws OverflowException {
        return this.cast(IntegerType.UI8);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractBoundedInt toIntegerValue() throws OverflowException {
        return this.cast(IntegerType.I32);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractBoundedInt toShortValue() throws OverflowException {
        return this.cast(IntegerType.I16);
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        if (!this.lower.isFinite() && !this.upper.isFinite()) {
            sb.append(AbstractBoundedInt.UNKNOWN_SIGN);
        } else {
            sb.append(this.lower.isFinite() ? "[" : "(");
            sb.append(this.lower.toString());
            sb.append(",");
            sb.append(this.upper.toString());
            sb.append(this.upper.isFinite() ? "]" : ")");
        }
        if (!this.containsZero
            && !this.lower.isZero()
            && !this.upper.isZero()
            && IntervalBoundedInt.containsZero(this.lower, this.upper))
        {
            sb.append(IntervalBoundedInt.NO_ZERO);
        }

        final boolean showLower = this.lowerCounter > 0 && this.lower.isFinite();
        final boolean showUpper = this.upperCounter > 0 && this.getUpper().isFinite();

        if (showLower && showUpper) {
            sb.append("(");
            sb.append(this.lowerCounter);
            sb.append(",");
            sb.append(this.upperCounter);
            sb.append(")");
        } else if (showLower) {
            sb.append("(l");
            sb.append(this.lowerCounter);
            sb.append(")");
        } else if (showUpper) {
            sb.append("(u");
            sb.append(this.upperCounter);
            sb.append(")");
        }

        if (!this.getMinLower().equals(this.lower) || !this.getMaxUpper().equals(this.upper)) {
            sb.append("{");
            sb.append(this.getMinLower().toString());
            sb.append(",");
            sb.append(this.getMaxUpper().toString());
            sb.append("}");
        }

        return sb.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractBoundedInt union(final AbstractBoundedInt o) {
        final IntervalBound newLow = this.lower.min(o.getLower());
        final IntervalBound newUp = this.upper.max(o.getUpper());
        final boolean newContainsZero = this.containsZero || o.containsLiteral(0);
        final int newLowerCounter = Math.max(this.lowerCounter, o.getLowerCounter());
        final int newUpperCounter = Math.max(this.upperCounter, o.getUpperCounter());
        return AbstractBoundedInt.create(
            newLow,
            newUp,
            newContainsZero,
            this.minimalLowerBound.min(o.getMinLower()),
            this.maximalUpperBound.max(o.getMaxUpper()),
            newLowerCounter,
            newUpperCounter);
    }

    /** {@inheritDoc} */
    @Override
    public AbstractBoundedInt ushr(final AbstractBoundedInt n, final IntegerType intType, final boolean ignoreOverflows) {
        if (n.isLiteral()) {
            final int literalValue = n.getLiteral().intValue();

            final int lowerBits;
            if (intType.getBitSize() == 64) {
                lowerBits = literalValue & 0x3f;
            } else {
                lowerBits = literalValue & 0x1f;
            }
            if (lowerBits == 0) {
                return this;
            }
        }

        final int newLowerCounter = Math.max(this.lowerCounter, n.getLowerCounter());
        final int newUpperCounter = Math.max(this.upperCounter, n.getUpperCounter());

        if (ignoreOverflows) {
            return AbstractBoundedInt.create(
                IntervalBound.ZERO,
                IntegerType.UNBOUND.getUpper(),
                true,
                this.minimalLowerBound,
                this.maximalUpperBound,
                newLowerCounter,
                newUpperCounter);
        } else {
            return AbstractBoundedInt.create(
                IntervalBound.ZERO,
                intType.getUpper(),
                true,
                this.minimalLowerBound,
                this.maximalUpperBound,
                newLowerCounter,
                newUpperCounter);
        }
    }

    /**
     * @return true iff the value was already widened in a merge
     */
    public boolean wasWidened() {
        return this.upperCounter > 0;
    }

    /** {@inheritDoc} */
    @Override
    public AbstractBoundedInt xor(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean ignoreOverflows)
    {
        if (sameReference) {
            return AbstractBoundedInt.getZero();
        }

        final int newLowerCounter = Math.max(this.lowerCounter, n.getLowerCounter());
        final int newUpperCounter = Math.max(this.upperCounter, n.getUpperCounter());

        final IntervalBound minLower = ignoreOverflows ? IntegerType.UNBOUND.getLower() : intType.getLower();
        final IntervalBound maxUpper = ignoreOverflows ? IntegerType.UNBOUND.getUpper() : intType.getUpper();

        if ((this.isNonNegative() && n.isNegative()) || (this.isNegative() && n.isNonNegative())) {
            // different sign bits -> 1 -> negative
            return AbstractBoundedInt.create(
                minLower,
                IntervalBound.NEGONE,
                false,
                this.minimalLowerBound.min(n.getMinLower()),
                this.maximalUpperBound.max(n.getMaxUpper()),
                newLowerCounter,
                newUpperCounter);
        }
        if ((this.isNegative() && n.isNegative()) || (this.isNonNegative() && n.isNonNegative())) {
            // same sign bits -> 0 -> nonnegative
            return AbstractBoundedInt.create(
                IntervalBound.ZERO,
                maxUpper,
                true,
                this.minimalLowerBound.min(n.getMinLower()),
                this.maximalUpperBound.max(n.getMaxUpper()),
                newLowerCounter,
                newUpperCounter);
        }
        if (ignoreOverflows) {
            return AbstractBoundedInt.getUnknown(IntegerType.UNBOUND);
        } else {
            return AbstractBoundedInt.getUnknown(intType);
        }
    }

    /**
     * Casts this AI to an int of the given type, preserving some bounds if possible.
     * @param intType target-type of the cast
     * @return new AI representing values within the range of the given type
     * @throws OverflowException iff the cast might result in loss of precision
     */
    private AbstractBoundedInt cast(final IntegerType intType) throws OverflowException {
        //Maybe we don't need to do anything:
        if (this.getLower().compareTo(intType.getLower()) >= 0 || this.getUpper().compareTo(intType.getUpper()) <= 0) {
            return this;
        }

        //Check out if the result will contain zero:
        final boolean newContainsZero =
            AbstractBoundedInt.overflowZeroTest(this.containsZero, intType, this.getLower(), this.getUpper());

        /*
         * Find out if we can do anything. We can do so if the representable part of the integer (in binary notation)
         * is equal for both the upper and lower bound and if after the cast, both have the same sign. If that is the
         * case, we copy the remainder of the common prefix after casting and extend it to the smallest number (for
         * the lower bound) and the biggest number).
         */
        final BigInteger oldLowBound = this.getLower().getConstant();
        final BigInteger oldUpBound = this.getUpper().getConstant();

        // Use xor to find differing bits, compute index of the leftmost bit that is differing
        int leftmostDiffIndex = Math.max(oldLowBound.bitLength(), oldUpBound.bitLength());
        final BigInteger differingBits = oldLowBound.xor(oldUpBound);
        while (!differingBits.testBit(leftmostDiffIndex) && leftmostDiffIndex >= 0) {
            leftmostDiffIndex--;
        }

        /*
         * If the index leftmost difference is smaller than the number of non-sign bits in the target type (i.e., the
         * common prefix is extending into the bits left after casting), we can provide a guestimate for the
         * resulting interval:
         */
        final int newTypeBitSize = intType.getBitSize();
        if (leftmostDiffIndex < newTypeBitSize - 1) {
            //Get the common sign:
            final StringBuilder commonPrefix = new StringBuilder(newTypeBitSize);
            final boolean isNegative = oldLowBound.testBit(newTypeBitSize - 1);

            //Check if this will actually be interpreted as sign or as part of the number:
            if (intType.isSigned()) {
                commonPrefix.setCharAt(0, isNegative ? '-' : '+');
            } else {
                commonPrefix.setCharAt(0, isNegative ? '1' : '0');
            }

            //Get the rest of the common prefix:
            for (int i = newTypeBitSize - 2; i > leftmostDiffIndex; i--) {
                commonPrefix.setCharAt(newTypeBitSize - 1 - i, oldLowBound.testBit(i) ? '1' : '0');
            }

            //Now build the smallest and biggest numbers with this prefix:
            final StringBuilder newLowerBoundRepr = new StringBuilder(commonPrefix.toString());
            final StringBuilder newUpperBoundRepr = new StringBuilder(commonPrefix.toString());
            /*
             * For negative number in a signed representation, adding 1 makes it smaller and 0 makes it bigger.
             * For positive numbers (either by 0 as sign bit or as unsigned numbers), adding a 0 makes it smaller
             * and 1 bigger.
             */
            final boolean oneIncreasesValue = !isNegative || !intType.isSigned();
            for (int i = leftmostDiffIndex; i >= 0; i++) {
                newLowerBoundRepr.setCharAt(newTypeBitSize - 1 - i, oneIncreasesValue ? '0' : '1');
                newUpperBoundRepr.setCharAt(newTypeBitSize - 1 - i, oneIncreasesValue ? '1' : '0');
            }

            final IntervalBound newLowBound = IntervalBound.create(new BigInteger(newLowerBoundRepr.toString(), 2));
            final IntervalBound newUpBound = IntervalBound.create(new BigInteger(newUpperBoundRepr.toString(), 2));

            final IntervalBoundedInt res =
                new IntervalBoundedInt(
                    newLowBound,
                    newUpBound,
                    newContainsZero,
                    newLowBound.min(this.getMinLower()),
                    newUpBound.max(this.getMaxUpper()),
                    this.getLowerCounter(),
                    this.getUpperCounter());

            throw new OverflowException(intType, null, res);
        } else {
            throw new OverflowException(intType, null, new IntervalBoundedInt(
                intType.getLower(),
                intType.getUpper(),
                newContainsZero,
                intType.getLower().min(this.getMinLower()),
                intType.getUpper().max(this.getMaxUpper()),
                this.getLowerCounter(),
                this.getUpperCounter()));
        }
    }

    @Override
    public boolean isNonZero() {
        // TODO Auto-generated method stub
        return !IntervalBoundedInt.containsZero(this.getLower(), this.getUpper()) || !this.containsZero;
    }
}
