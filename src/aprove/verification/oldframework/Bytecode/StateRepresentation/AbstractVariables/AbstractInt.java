package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Parent class of all int/long value representations in our symbolic
 * interpretation.
 * @author Carsten Otto, Marc Brockschmidt
 */
public abstract class AbstractInt extends AbstractNumber {

    /**
     * The prefix for values with unknown sign
     */
    static final String UNKNOWN_SIGN = "#";

    /**
     * After how many simple merges do we need to introduce infinity?
     * COUNTER_MAX = 0 means [1,1] and [2,2] is directly merged to [1,inf).
     */
    private static final int COUNTER_MAX = 2;

    /**
     * Finds the strongest relation between a and b
     * @param a
     * @param b
     * @return the most strict relation between a and b or null of none can be found
     */
    public static IntegerRelationType computeRelationType(
        final AbstractInt a,
        final AbstractInt b
    ) {
        //EQ, only possible for literals
        if (a.isLiteral() && b.isLiteral() && a.getLiteral().compareTo(b.getLiteral()) ==0) {
            return IntegerRelationType.EQ;
        }
        //GT, GE
        int resG = a.getLower().compareTo(b.getUpper());
        if (resG > 0) {
            return IntegerRelationType.GT;
        } else if (resG >= 0) {
            return IntegerRelationType.GE;
        }
        //LT, LE
        int resL = a.getUpper().compareTo(b.getLower());
        if (resL < 0) {
            return IntegerRelationType.LT;
        } else if (resL <= 0) {
            return IntegerRelationType.LE;
        }
        //nothing
        return null;
    }

    /**
     * Check if a compT b is true.
     * @param intRel an {@link IntArithmetic} comparison
     * @param a one AbstractInt
     * @param b another AbstractInt
     * @param sameRef true only if the two integers are referenced from the same
     * references
     * @param areDefinitelyUnequal true if the two integers cannot be the same
     * @return true only if a compT b holds. False may be returned if we do not
     * know the result.
     */
    public static boolean computeComparisonResult(
        final IntegerRelationType intRel,
        final AbstractInt a,
        final AbstractInt b,
        final boolean sameRef,
        final boolean areDefinitelyUnequal)
    {
        // Do the easy case first. Literals:
        if (a.isLiteral() && b.isLiteral()) {
            final int cmp = a.getLiteral().compareTo(b.getLiteral());
            switch (intRel) {
            case EQ:
                return cmp == 0;
            case NE:
                return cmp != 0;
            case GE:
                return cmp >= 0;
            case LE:
                return cmp <= 0;
            case GT:
                return cmp > 0;
            case LT:
                return cmp < 0;
            default:
                assert (false);
            }
        }

        // Another easy case: Same references:
        if (sameRef) {
            switch (intRel) {
            case GE:
            case LE:
            case EQ:
                return true;
            case GT:
            case LT:
            case NE:
                return false;
            default:
                assert (false) : "Unknown Integer relation type";
                return false;
            }
        }

        final Integer cmp = a.compareToApprox(b);
        if (cmp != null) {
            switch (intRel) {
            case GT:
                return cmp > 0;
            case GE:
                return cmp >= 0;
            case LT:
                return cmp < 0;
            case LE:
                return cmp <= 0;
            case NE:
                return cmp != 0;
            case EQ:
                return cmp == 0;
            default:
                assert (false);
            }
        }

        if (intRel == IntegerRelationType.LE) {
            if (a.getUpper().equals(b.getLower())) {
                return true;
            }
        }
        if (intRel == IntegerRelationType.LT) {
            //Only one common number, but they are unequal => Good:
            if (a.getUpper().equals(b.getLower()) && areDefinitelyUnequal) {
                return true;
            }
        }

        if (intRel == IntegerRelationType.GE) {
            if (b.getUpper().equals(a.getLower())) {
                return true;
            }
        }
        if (intRel == IntegerRelationType.GT) {
            //Only one common number, but they are unequal => Good:
            if (b.getUpper().equals(a.getLower()) && areDefinitelyUnequal) {
                return true;
            }
        }

        if (intRel == IntegerRelationType.NE) {
            if (b.isZero() && !a.containsLiteral(0)) {
                return true;
            }
            if (a.isZero() && !b.containsLiteral(0)) {
                return true;
            }
        }

        return false;
    }

    /**
     * @param literal the literal value of the created AbstractInt
     * @return an abstract int representing the given value
     */
    public static LiteralInt create(final BigInteger literal) {
        return LiteralInt.createLiteralInt(literal);
    }

    /**
     * @param low the lower bound of the interval
     * @param up the upper bound of the interval
     * @param containsZero true iff zero should be represented
     * @param newLowerCounter how often the interval was widened towards the lower during abstraction.
     * @param newUpperCounter how often the interval was widened towards the upper during abstraction.
     * @param minLow the minimal lower bound used for this interval in its arithmetic history.
     *  If <code>low</code> is smaller, it is used instead.
     * @param maxUp the maximal upper bound used for this interval in its arithmetic history
     *  If <code>up</code> is bigger, it is used instead.
     * @return an abstract int representing the values between the two bounds,
     *  where zero may be excluded.
     */
    public static AbstractInt create(
        final IntervalBound low,
        final IntervalBound up,
        final boolean containsZero,
        final IntervalBound minLow,
        final IntervalBound maxUp,
        final int newLowerCounter,
        final int newUpperCounter)
    {
        final AbstractInt res;
        if (low.equals(up)) {
            assert (!up.isZero() || containsZero);
            res = LiteralInt.createLiteralInt(up.getConstant());
        } else {
            res = new IntervalInt(low, up, containsZero, minLow, maxUp, newLowerCounter, newUpperCounter);
        }
        assert (res.getLower().compareTo(res.getUpper()) <= 0);
        return res;
    }

    /**
     * @param low the lower bound of the interval
     * @param up the upper bound of the interval
     * @param minLow the minimal lower bound used for this interval in its arithmetic history.
     *  If <code>low</code> is smaller, it is used instead.
     * @param maxUp the maximal upper bound used for this interval in its arithmetic history
     *  If <code>up</code> is bigger, it is used instead.
     *  neither an Integer, nor a long
     * @param newLowerCounter how often the interval was widened towards the lower during abstraction.
     * @param newUpperCounter how often the interval was widened towards the upper during abstraction.
     * @return an abstract int representing the values between the two bounds,
     *  where zero may be excluded.
     */
    public static AbstractInt create(
        final IntervalBound low,
        final IntervalBound up,
        final IntervalBound minLow,
        final IntervalBound maxUp,
        final int newLowerCounter,
        final int newUpperCounter)
    {
        final boolean containsZero = IntervalInt.containsZero(low, up);
        return AbstractInt.create(low, up, containsZero, minLow, maxUp, newLowerCounter, newUpperCounter);
    }

    /**
     * @param literal the literal value of the created AbstractInt
     * @return an abstract int representing the given value
     */
    public static LiteralInt create(final long literal) {
        return LiteralInt.createLiteralInt(literal);
    }

    /**
     * @return AI representing -1.
     */
    public static final LiteralInt getMOne() {
        return new LiteralInt(BigInteger.ONE.negate());
    }

    /**
     * @return AI representing 1
     */
    public static final LiteralInt getOne() {
        return new LiteralInt(BigInteger.ONE);
    }

    /**
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return AI representing an arbitrary value (with correct bounds, however)
     */
    public static IntervalInt getUnknown(final IntegerType intType) {
        return new IntervalInt(intType);
    }

    /**
     * @return AI representing 0.
     */
    public static final LiteralInt getZero() {
        return new LiteralInt(BigInteger.ZERO);
    }

    /**
     * Check if a compT b is decidable, i.e. we know that a compT b holds or a
     * invCompT b holds (where invCompT is the inverse of compT).
     * @param intRel an {@link IntArithmetic} comparison
     * @param a one AbstractInt
     * @param b another AbstractInt
     * @param sameRef true only if the two integers are referenced from the same
     * references
     * @param areUnequal true if the two integers cannot be the same
     * @return true if a compT b can be decided
     */
    public static boolean isDecidableComparison(
        final IntegerRelationType intRel,
        final AbstractInt a,
        final AbstractInt b,
        final boolean sameRef,
        final boolean areUnequal)
    {

        final IntegerRelationType intRelInv = intRel.invert();
        return (AbstractInt.computeComparisonResult(intRel, a, b, sameRef, areUnequal) || AbstractInt
            .computeComparisonResult(intRelInv, a, b, sameRef, areUnequal));
    }

    /**
     * Combines the min/max bounds as well as counters from the two given ints, creating a new AbstracInt with the given values
     * @param low the lower bound of the interval
     * @param up the upper bound of the interval
     * @param containsZero whether the interval may include zero
     * @param first the first Abstract int that is combined
     * @param second the second Abstract int that is combined
     * @return
     */
    protected static AbstractInt combine(
        IntervalBound low,
        IntervalBound up,
        boolean containsZero,
        IntervalInt first,
        AbstractInt second,
        IntegerType intType
    ) {
        IntervalBound minLow, maxUp;
        if (second.isLiteral()) {
            minLow = first.getMinLower();
            maxUp = first.getMaxUpper();
        } else {
            minLow = first.getMinLower().min(second.getMinLower());
            maxUp = first.getMaxUpper().max(second.getMaxUpper());
        }
        int lowerCounter = Math.max(first.getLowerCounter(), second.getLowerCounter());
        int upperCounter = Math.max(first.getUpperCounter(), second.getUpperCounter());

        AbstractInt res = AbstractInt.create(low, up, containsZero, minLow, maxUp, lowerCounter, upperCounter);
        if (res.equalsOnlyRepresentedValues(first)) {
            return first;
        }
        if (second.isLiteral()) {
            res.copyComparisonsFrom(first);
        }
        return res;
    }

    /**
     * Combines the min/max bounds as well as counters from the two given ints, creating a new AbstracInt with the given values
     * @param low the lower bound of the interval
     * @param up the upper bound of the interval
     * @param first the first Abstract int that is combined
     * @param second the second Abstract int that is combined
     * @return
     */
    protected static AbstractInt combine(
        IntervalBound low,
        IntervalBound up,
        IntervalInt first,
        AbstractInt second,
        IntegerType intType
    ) {
        boolean containsZero = IntervalInt.containsZero(low, up);
        return AbstractInt.combine(low, up, containsZero, first, second, intType);
    }

    /**
     * Test whether this abstract int might represent zero after a a cast.
     * @param containedZero whether the AI might have been zero before the overflow
     * @param intType Type of the integer after casting
     * @param low the lower bound of the AI, possibly smaller than the the smallest valid value for the given
     *  {@code intType}
     * @param up the upper bound of the AI, possibly larger than the the largest valid value for the given
     *  {@code intType}
     * @return whether the AI might be zero after the overflow
     */
    protected static boolean overflowZeroTest(
        final boolean containedZero,
        final IntegerType intType,
        final IntervalBound low,
        final IntervalBound up)
    {
        if (containedZero) {
            return true;
        }

        /* Idea:
         *  Take the lower bound, get its bit pattern. Find the next higher or equal number which has
         *  intType.getBitSize() bits set to 0 at the end. Check if it is smaller than the upper bound:
         * (1) The equal case. Check if low & (2^(bitSize)-1) == 0. If yes, we are done.
         * (2) The bigger case. Check if low + 2^(bitSize) & (2^(bitSize)-1) < up. If yes, 0 will be included.
         */

        final BigInteger endOnes = BigInteger.valueOf(2).pow(intType.getBitSize() - 1);
        if (low.getConstant().and(endOnes).equals(BigInteger.ZERO)) {
            return true;
        }

        if (low
            .getConstant()
            .add(BigInteger.valueOf(2).pow(intType.getBitSize()))
            .and(endOnes)
            .compareTo(up.getConstant()) < 0)
        {
            return true;
        }

        return false;
    }

    /**
     * Comparisons performed with the encoded value, such that for every pair ($rel, $val) we checked $this $rel $val.
     * Here, $val is some constant.
     */
    private final Set<Pair<IntegerRelationType, BigInteger>> wasComparedTo = new LinkedHashSet<>();

    /**
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return AbstractInt representing all absolute values of values represented by this
     */
    public abstract AbstractInt absolute(final IntegerType intType);

    /**
     * Creates a new AbstractInt from the sum of two existing AbstractInts.
     * @param n value to be added to this
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return sum of this instance and the argument
     */
    public abstract AbstractInt add(final AbstractInt n, final IntegerType intType);

    /**
     * Creates a new AbstractInt by applying logical AND to the two existing
     * AbstractInts.
     * @param n value to be ANDed to this
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param sameReference true iff both operands are the very same value.
     * @return logical AND of this instance and the argument
     */
    public abstract AbstractInt and(
            final AbstractInt n,
            final boolean sameReference,
            final IntegerType intType);

    /**
     * Try to compare to given AbstractInt to this. For -1, 0, 1 this
     * corresponds to compareTo. For null we do not know the result. In most
     * cases you should make use of "computeComparisonResult" which may give
     * positive answers for some relations even if the comparison cannot be
     * decided.
     * @param other compare to this AbstractInt
     * @return -1, 0, 1 or null.
     */
    public abstract Integer compareToApprox(AbstractInt other);

    /**
     * @param other another AI
     * @return true iff other is contained in the interval specified by this
     */
    public abstract boolean containsInt(final AbstractInt other);

    /**
     * @param i Integer to be checked
     * @return true iff i is contained in the interval specified by this
     */
    public abstract boolean containsLiteral(final BigInteger i);

    /**
     * @param i Integer to be checked
     * @return true iff i is contained in the interval specified by this
     */
    public final boolean containsLiteral(final int i) {
        return this.containsLiteral(BigInteger.valueOf(i));
    }

    /**
     * Creates a new AbstractInt by dividing all values from this by all values
     * from the argument using integer division (rounding towards zero).
     * @param n value to be used as divisor
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return AbstractInt obtained by dividing values from this AbstractInt by values from n. If n can be 0, the first
     *         boolean value is set to true and indicates a possible ArithmeticException. If n is equal to 0 the
     *         returned AbstractInt is null and only the exception must be thrown (the first boolean value is still set
     *         to true). If the result represents values which are obtained by rounding towards zero (i.e., they do not
     *         correspond to exact division on real numbers), the second boolean value is set to true.
     */
    public Triple<? extends AbstractInt, Boolean, Boolean> div(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType)
    {
        //If we only have a division by zero, do a shortcut here:
        if (n.isZero()) {
            return new Triple<AbstractInt, Boolean, Boolean>(null, Boolean.TRUE, Boolean.FALSE);
        }
        AbstractInt res = null;
        final boolean nContainsZero = n.containsLiteral(0);
        final boolean rounded;
        // first, some special cases
        if (sameReference) {
            // a/a = 1:
            res = AbstractInt.getOne();
            rounded = false;
        } else if (n.isOne()) {
            // Division by 1
            res = this;
            rounded = false;
        } else if (n.isNegOne()) {
            // Division by -1
            res = this.negate(intType);
            rounded = false;
        } else {
            // Now, do the exact computation
            final AbstractInt thisAbs = this.absolute(IntegerType.UNBOUND);
            final AbstractInt thatAbs = n.absolute(IntegerType.UNBOUND).removeZeroFromInteger();
            final IntervalBound absMin = thisAbs.getLower().divide(thatAbs.getUpper());
            final IntervalBound absMax = thisAbs.getUpper().divide(thatAbs.getLower());
            final boolean thisNonNegative = this.isNonNegative();
            final boolean thisNegative = this.isNegative();
            final boolean thatNonNegative = n.isNonNegative();
            final boolean thatNegative = n.isNegative();
            // Now compute the signs for the final bounds:
            final IntervalBound resMin;
            final IntervalBound resMax;
            if ((thisNegative && thatNegative) || (thisNonNegative && thatNonNegative)) {
                // both have the same sign: result is positive
                resMin = absMin;
                resMax = absMax;
            } else if ((thisNegative && thatNonNegative) || (thisNonNegative && thatNegative)) {
                // the signs differ: result is negative
                resMin = absMax.negate();
                resMax = absMin.negate();
            } else {
                // no clue about the signs
                resMin = absMax.negate();
                resMax = absMax;
            }
            final int newLowerCounter = Math.max(this.getLowerCounter(), n.getLowerCounter());
            final int newUpperCounter = Math.max(this.getUpperCounter(), n.getUpperCounter());
            // The result, mathematically correct:
            res =
                AbstractInt.create(
                    resMin,
                    resMax,
                    this.getMinLower(),
                    this.getMaxUpper(),
                    newLowerCounter,
                    newUpperCounter);
            // assuming that rounding occurs is sound and will be true in almost every case (for literals, this method
            // is overridden)
            rounded = true;
        }
        return new Triple<AbstractInt, Boolean, Boolean>(res, nContainsZero, rounded);
    }

    /**
     * This is like the standards equals, but it ignores the counters for the number of bound extensions (i.e., only
     * looks at the actual values).
     * @param obj some other object
     * @return true if the represented values are the same
     */
    public abstract boolean equalsOnlyRepresentedValues(final Object obj);

    /**
     * Returns the bounds to which we already compared our integers.
     *
     * @return a set of integer values against which this interval was compared
     */
    public Set<Pair<IntegerRelationType, BigInteger>> getComparedValues() {
        return new LinkedHashSet<>(this.wasComparedTo);
    }

    /**
     * @return the literal value of this AbstractInt (if it exists)
     */
    public abstract BigInteger getLiteral();

    /**
     * @return the smallest number represented by this AbstractInt (may be
     * -infty)
     */
    public abstract IntervalBound getLower();

    /**
     * @return how often this integer was widened towards the lower bound during
     * abstraction.
     */
    public abstract int getLowerCounter();

    /**
     * @return the biggest number ever represented by this AbstractInt
     * in its arithmetic history (may be -infty)
     */
    public abstract IntervalBound getMaxUpper();

    /**
     * @return the smallest number ever represented by this AbstractInt
     * in its arithmetic history (may be -infty)
     */
    public abstract IntervalBound getMinLower();

    /**
     * @return the largest number represented by this AbstractInt (may be
     * +infty)
     */
    public abstract IntervalBound getUpper();

    /**
     * @return how often this integer was widened towards the upper bound during
     * abstraction.
     */
    public abstract int getUpperCounter();

    /**
     * @return True if all values represented by this AbstractInt are bigger than one (&gt;1)
     */
    public abstract boolean isBiggerOne();

    /**
     * @return true if all values represented by this AbstractInt are negative
     * (&lt;0)
     */
    public abstract boolean isNegative();

    /**
     * @return if this AbstractInt represents -1
     */
    public abstract boolean isNegOne();

    /**
     * @return true if all values represented by this AbstractInt are
     * non-negative (&ge;0)
     */
    public abstract boolean isNonNegative();

    /**
     * @return true if all values represented by this AbstractInt are
     * non-negative (&le;0)
     */
    public abstract boolean isNonPositive();

    /**
     * @return if this AbstractInt represents 1
     */
    public abstract boolean isOne();

    /**
     * @return true if all values represented by this AbstractInt are positive
     * (&gt;0)
     */
    public abstract boolean isPositive();

    /**
     * @return True if all values represented by this AbstractInt are smaller than minus one (&lt;-1)
     */
    public abstract boolean isSmallerMinusOne();

    /**
     * @return if this AbstractInt represents 0
     */
    public abstract boolean isZero();

    public AbstractNumberMergeResult merge(final AbstractNumber otherVar, final boolean increaseCounters, final IntegerType intType) {
    	return merge(otherVar, increaseCounters, intType, COUNTER_MAX);
    }
    
    /**
     * Merge the values represented by this {@link AbstractInt} with another one.
     * @param otherVar the {@link AbstractInt} to merge with
     * @return an {@link AbstractNumberMergeResult}, holding an
     * {@link AbstractVariable} that represents all values that are represented
     * by this and otherVar, costs to obtain this merged result and pointers to
     * the original variables.
     * 
     * @param mergeToExtremeValCountThreshold After how many simple merges do we need to introduce infinity?
     */
    public AbstractNumberMergeResult merge(
        final AbstractNumber otherVar,
        final boolean increaseCounters,
        final IntegerType intType,
        final int mergeToExtremeValCountThreshold
    ) {
        if (this.equalsOnlyRepresentedValues(otherVar)) {
            final AbstractNumberMergeResult r = new AbstractNumberMergeResult(this, otherVar);
            r.setMergedVariable(this);
            r.setVarAtoMerged(CostType.NONE);
            r.setVarBtoMerged(CostType.NONE);
            return r;
        }

        if (!(otherVar instanceof AbstractInt)) {
            throw new IllegalArgumentException("Parameter needs to be " + "AbstractInt");
        }
        final AbstractInt that = (AbstractInt) otherVar;

        // If the other is not this the result will be the union.
        final AbstractNumberMergeResult result = new AbstractNumberMergeResult(this, that);

        AbstractInt resultVar = this.union(that);

        final boolean thisLowerBoundChanged = !this.getLower().equals(resultVar.getLower());
        final boolean thisUpperBoundChanged = !this.getUpper().equals(resultVar.getUpper());
        final boolean thisZeroChanged = this.containsLiteral(0) != resultVar.containsLiteral(0);
        final boolean thatLowerBoundChanged = !that.getLower().equals(resultVar.getLower());
        final boolean thatUpperBoundChanged = !that.getUpper().equals(resultVar.getUpper());
        final boolean thatZeroChanged = that.containsLiteral(0) != resultVar.containsLiteral(0);

        final boolean thisChangedToInfinity =
            (thisLowerBoundChanged && resultVar.getLower().equals(intType.getLower()))
                || (thisUpperBoundChanged && resultVar.getUpper().equals(intType.getUpper()));
        final boolean thisChanged = thisZeroChanged || thisLowerBoundChanged || thisUpperBoundChanged;
        final boolean thatChangedToInfinity =
            (thatLowerBoundChanged && resultVar.getLower().equals(intType.getLower()))
                || (thatUpperBoundChanged && resultVar.getUpper().equals(intType.getUpper()));
        final boolean thatChanged = thatZeroChanged || thatLowerBoundChanged || thatUpperBoundChanged;

        // cost compared to this
        if (thisChangedToInfinity) {
            // some infinite bound was added
            result.setVarAtoMerged(CostType.INTERVAL_INFINITE);
        } else if (thisChanged) {
            // we only introduced new finite bounds
            result.setVarAtoMerged(CostType.INTERVAL_FINITE);
        } else {
            result.setVarAtoMerged(CostType.NONE);
        }

        // cost compared to that
        if (thatChangedToInfinity) {
            // some infinite bound was added
            result.setVarBtoMerged(CostType.INTERVAL_INFINITE);
        } else if (thatChanged) {
            // we only introduced new finite bounds
            result.setVarBtoMerged(CostType.INTERVAL_FINITE);
        } else {
            result.setVarBtoMerged(CostType.NONE);
        }

        int newLowerCounter = resultVar.getLowerCounter();
        if (thisLowerBoundChanged || thatLowerBoundChanged) {
            newLowerCounter++;
        }

        int newUpperCounter = resultVar.getUpperCounter();
        if (thisUpperBoundChanged || thatUpperBoundChanged) {
            newUpperCounter++;
        }

        // increase the counter if we had to change something
        if (increaseCounters) {
            resultVar =
                AbstractInt.create(
                    resultVar.getLower(),
                    resultVar.getUpper(),
                    resultVar.containsLiteral(0),
                    resultVar.getMinLower(),
                    resultVar.getMaxUpper(),
                    newLowerCounter,
                    newUpperCounter);
        }

        if (resultVar.getUpperCounter() > mergeToExtremeValCountThreshold
            && !resultVar.getUpper().equals(that.getMaxUpper())
            && !resultVar.getUpper().equals(resultVar.getMaxUpper())
            && resultVar.getUpper().compareTo(resultVar.getMaxUpper()) < 0
            && that.getLower().equals(resultVar.getLower())
            && that.getUpper().compareTo(resultVar.getUpper()) < 0)
        {
            IntervalBound newUpperBound = intType.getUpper();

            //Try to guess a better upper bound:
            if (this instanceof IntervalInt) {
                /* Try to base this on all concrete values against this
                 * was compared. Get all of them; check if they are big
                 * enough to serve as new upper bound; get the minimum of
                 * those matching these criteria.
                 */
                final Set<Pair<IntegerRelationType, BigInteger>> thisComparisons =
                    ((IntervalInt) this).getComparedValues();

                for (final Pair<IntegerRelationType, BigInteger> comparisons : thisComparisons) {
                    IntervalBound comparedBound = null;
                    /* If we had this <= [c,c], try to extend this to
                     * [foo, c+1]. If the comparison is repeated, there will
                     * be a refine for [foo, c] for the TRUE case and
                     * [c+1,c+1] for the FALSE case.
                     */
                    if (comparisons.x == IntegerRelationType.GT || comparisons.x == IntegerRelationType.LE) {
                        comparedBound = IntervalBound.create(comparisons.y.add(BigInteger.ONE));
                    }
                    /* If we had this < [c,c], try to extend this to
                     * [foo, c], if the comparison is repeated, there will
                     * be a refine to [foo,c) for the TRUE case and [c,c]
                     * for FALSE.
                     */
                    if (comparisons.x == IntegerRelationType.GE || comparisons.x == IntegerRelationType.LT) {
                        comparedBound = IntervalBound.create(comparisons.y);
                    }
                    if (comparedBound != null
                        && comparedBound.compareTo(resultVar.getUpper()) > 0
                        && comparedBound.compareTo(newUpperBound) < 0)
                    {
                        newUpperBound = comparedBound;
                    }
                }
            }
            resultVar =
                AbstractInt.create(
                    resultVar.getLower(),
                    newUpperBound,
                    resultVar.containsLiteral(0) || newUpperBound.isZero(),
                    resultVar.getMinLower(),
                    resultVar.getMaxUpper(),
                    resultVar.getLowerCounter(),
                    resultVar.getUpperCounter());
            result.setEnforcedWideningCost(CostType.INTERVAL_INFINITE);
        } else if (resultVar.getUpperCounter() > mergeToExtremeValCountThreshold
            && !resultVar.getUpper().equals(intType.getUpper())
            && !(resultVar.getUpper().equals(this.getMaxUpper()) && resultVar.getUpper().equals(that.getMaxUpper())))
        {
            /* We have no idea where to go, but our current upper bound is bigger
             * than one of the maximal upper bound we had earlier. Try going to +inf.
             */
            resultVar =
                AbstractInt.create(
                    resultVar.getLower(),
                    intType.getUpper(),
                    resultVar.containsLiteral(0),
                    resultVar.getMinLower(),
                    resultVar.getMaxUpper(),
                    resultVar.getLowerCounter(),
                    resultVar.getUpperCounter());
            result.setEnforcedWideningCost(CostType.INTERVAL_INFINITE);
        }
        if (resultVar.getLowerCounter() > mergeToExtremeValCountThreshold
            && !resultVar.getLower().equals(intType.getLower())
            && resultVar.getLower().compareTo(resultVar.getMinLower()) > 0
            && that.getLower().compareTo(resultVar.getLower()) > 0
            && that.getUpper().equals(resultVar.getUpper()))
        {
            /*
             * this [4, 8] and that [8, 16] are merged to [4, 16]
             * that.lower:  8 >  4
             * that.upper: 16 = 16
             * => go towards the maximal next suspected lower bound, or -inf
             */
            IntervalBound newLowerBound = intType.getLower();

            //Try to guess a better lower bound:
            if (this instanceof IntervalInt) {
                /* Try to base this on all concrete values against this
                 * was compared. Get all of them; check if they are
                small
                 * enough to serve as new lower bound; get the maximum
                of
                 * those matching these criteria.
                 */
                final Set<Pair<IntegerRelationType, BigInteger>> thisComparisons =
                    ((IntervalInt) this).getComparedValues();

                for (final Pair<IntegerRelationType, BigInteger> comparisons : thisComparisons) {
                    IntervalBound comparedBound = null;
                    /* If we had this <= [c,c], try to extend this to
                     * [c, foo]. If the comparison is repeated, there will
                     * be a refine for [c, c] for the TRUE case and
                     * (c, foo] for the FALSE case.
                     */
                    if (comparisons.x == IntegerRelationType.GT || comparisons.x == IntegerRelationType.LE) {
                        comparedBound = IntervalBound.create(comparisons.y);
                    }
                    /* If we had this < [c,c], try to extend this to
                     * [c-1, foo], if the comparison is repeated, there will
                     * be a refine to [c-1,c-1] for the TRUE case and
                     * [c, foo] for FALSE.
                     */
                    if (comparisons.x == IntegerRelationType.GE || comparisons.x == IntegerRelationType.LT) {
                        comparedBound = IntervalBound.create(comparisons.y.subtract(BigInteger.ONE));
                    }
                    if (comparedBound != null
                        && comparedBound.compareTo(resultVar.getLower()) < 0
                        && comparedBound.compareTo(newLowerBound) > 0)
                    {
                        newLowerBound = comparedBound;
                    }
                }
            }
            resultVar =
                AbstractInt.create(
                    newLowerBound,
                    resultVar.getUpper(),
                    resultVar.containsLiteral(0) || newLowerBound.isZero(),
                    resultVar.getMinLower(),
                    resultVar.getMaxUpper(),
                    resultVar.getLowerCounter(),
                    resultVar.getUpperCounter());
            result.setEnforcedWideningCost(CostType.INTERVAL_INFINITE);
        } else if (resultVar.getLowerCounter() > mergeToExtremeValCountThreshold
            && !(resultVar.getLower().equals(this.getMinLower()) && resultVar.getLower().equals(that.getMinLower())))
        {
            /* We have no idea where to go, but our current lower bound is smaller
             * than one of the minimal lower bound we had earlier. Try going to -inf.
             */
            resultVar = AbstractInt.getUnknown(intType);
            result.setEnforcedWideningCost(CostType.INTERVAL_INFINITE);
        } else {
            //System.err.println("Not widening interval!");
        }
        if (intType == IntegerType.UNBOUND_POSITIVE) {
            resultVar = resultVar.onlyPositive();
        } else if (intType == IntegerType.UNBOUND_NON_NEGATIVE) {
            resultVar = resultVar.onlyNonNegative();
        }
        result.setMergedVariable(resultVar);
        return result;
    }

    /**
     * Creates an AbstractInt by multiplying all values from this by all values
     * from the argument.
     * @param n value to be multiplied
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return AbstractInt of values obtained by multiplying values from this AbstractInt with values from n
     */
    public abstract AbstractInt mul(final AbstractInt n, final IntegerType intType);

    /**
     * Creates an AbstractInt by negating all values in this AbstractInt.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return negated AbstractInt
     */
    public abstract AbstractInt negate(final IntegerType intType);

    /**
     * Note that this interval was compared with the value i (in a loop condition, for example)
     * @param rel type of integer relation, oriented such that the performed
     *  comparison was $this $rel $i.
     * @param i some integer
     */
    public void noteComparisonWith(final IntegerRelationType rel, final BigInteger i) {
        this.wasComparedTo.add(new Pair<>(rel, i));
    }

    /**
     * @return an AbstractInt that only contains the negative values of this
     */
    public AbstractInt onlyNegative() {
        assert (!this.isNonNegative());
        return AbstractInt.create(
            this.getLower(),
            this.getUpper().min(IntervalBound.NEGONE),
            false,
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());
    }

    /**
     * @return an AbstractInt that only contains the nonnegative values of this
     */
    public AbstractInt onlyNonNegative() {
        assert (!this.isNegative());
        return AbstractInt.create(
            this.getLower().max(IntervalBound.ZERO),
            this.getUpper(),
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());

    }

    /**
     * @return an AbstractInt that only contains the non-positive values of this
     */
    public AbstractInt onlyNonPositive() {
        assert (!this.isPositive());
        return AbstractInt.create(
            this.getLower(),
            this.getUpper().min(IntervalBound.ZERO),
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());

    }

    /**
     * @return an AbstractInt that only contains the positive values of this
     */
    public AbstractInt onlyPositive() {
        assert (!this.isNonPositive());
        return AbstractInt.create(
            this.getLower().max(IntervalBound.ONE),
            this.getUpper(),
            false,
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());
    }

    /**
     * Creates a new AbstractInt by applying logical OR to the two existing
     * AbstractInts.
     * @param n value to be ORed to this
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return logical OR of this instance and the argument
     */
    public abstract AbstractInt or(
            final AbstractInt n,
            final boolean sameReference,
            final IntegerType intType);

    /**
     * Creates a new AbstractInt with all possible remainders of a modulo b, where a is in this interval and b in the
     * AbstractInt passed as argument.
     * Warning: This method works fine for analyzing JBC and LLVM, but be aware of the fact that different remainder
     * implementations are out there when using this method for analyzing something else!
     * @param n value to be multiplied
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return AbstractInt of values obtained by modulo operations between this
     * and the values from n. If b can be 0, the boolean value is set to true
     * and indicates a possible ArithmeticException. If b is equal to 0 the
     * returned AbstractInt is null and only the exception must be thrown.
     */
    public Pair<? extends AbstractInt, Boolean> rem(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType)
    {
        // If we only have a division by zero, do a shortcut here:
        if (n.isZero()) {
            return new Pair<>(null, Boolean.TRUE);
        }

        final boolean oContainsZero = n.containsLiteral(0);
        // If this == 0, we know the result:
        if (this.isZero()) {
            return new Pair<>(AbstractInt.getZero(), oContainsZero);
        }

        if (sameReference) {
            // a % a = 0
            return new Pair<>(AbstractInt.getZero(), oContainsZero);
        }
        if (n.isOne()) {
            // a % 1 = 0
            return new Pair<>(AbstractInt.getZero(), Boolean.FALSE);
        }

        // x%y = x - ((x/y) * y) = x + (-((x/y) * y)) = x + ((x/y) * (-y))
        // Compute the exact values (will not throw an exception):
        final Triple<? extends AbstractInt, Boolean, Boolean> xDivY =
                this.div(n, sameReference, IntegerType.UNBOUND);
        assert (xDivY.y.equals(Boolean.valueOf(oContainsZero)));

        final AbstractInt yNeg = n.negate(IntegerType.UNBOUND);

        final AbstractInt xDivYTimesYNeg = xDivY.x.mul(yNeg, IntegerType.UNBOUND);

        final AbstractInt mid = xDivYTimesYNeg.add(this, IntegerType.UNBOUND);

        /*
         * [...] the result of the remainder operation can be negative only if
         * the dividend is negative and can be positive only if the dividend is
         * positive.
         *  -- JVMS, documentation of the irem opcode
         */
        IntervalBound resLow = mid.getLower().max(n.getUpper().abs().negate().add(IntervalBound.ONE));
        IntervalBound resUp = mid.getUpper().min(n.getUpper().abs().add(IntervalBound.ONE.negate()));
        if (this.isNonNegative()) {
            resLow = resLow.max(IntervalBound.ZERO);
            if (n.isLiteral()) {
                resUp = n.getLower().abs().add(IntervalBound.NEGONE);
            }
        } else if (this.isNonPositive()) {
            if (n.isLiteral()) {
                resLow = n.getLower().abs().negate().add(IntervalBound.ONE);
            }
            resUp = resUp.min(IntervalBound.ZERO);
        }

        final int newLowerCounter = Math.max(this.getLowerCounter(), n.getLowerCounter());
        final int newUpperCounter = Math.max(this.getUpperCounter(), n.getUpperCounter());

        final AbstractInt res =
                AbstractInt.create(
                        resLow,
                        resUp,
                        this.getMinLower(),
                        this.getMaxUpper(),
                        newLowerCounter,
                        newUpperCounter);

        return new Pair<>(res, oContainsZero);
    }

    /**
     * Remove zero from this.
     * @return a possibly modified AbstractInt
     */
    public abstract AbstractInt removeZeroFromInteger();

    /**
     * @return True if both lower and upper bounds of this abstract int are finite (i.e., it represents only finitely
     *         many numbers). False otherwise.
     */
    public boolean representsFinitelyManyNumbers() {
        return this.getLower().isFinite() && this.getUpper().isFinite();
    }

    /**
     * @param newLow The new lower bound.
     * @return An AbstractInt with its lower bound set to the specified bound and everything else as in the current
     *         AbstractInt if the new lower bound is consistent with (i.e., <=) the upper bound. Null otherwise.
     */
    public AbstractInt setLower(final IntervalBound newLow) {
        if (newLow.compareTo(this.getUpper()) > 0) {
            return null;
        }
        return AbstractInt.create(
            newLow,
            this.getUpper(),
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());
    }

    /**
     * @param newUp The new upper bound.
     * @return An AbstractInt with its upper bound set to the specified bound and everything else as in the current
     *         AbstractInt if the new upper bound is consistent with (i.e., >=) the lower bound. Null otherwise.
     */
    public AbstractInt setUpper(final IntervalBound newUp) {
        if (newUp.compareTo(this.getLower()) < 0) {
            return null;
        }
        return AbstractInt.create(
            this.getLower(),
            newUp,
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());
    }

    /**
     * Creates a new AbstractInt by shifting the bits representing this instance
     * to the left as often as the argument specifies.
     * @param n number of shift operations
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return shifted result
     */
    public abstract AbstractInt shl(final AbstractInt n, final IntegerType intType);

    /**
     * Creates a new AbstractInt by shifting the bits representing this instance
     * to the right as often as the argument specifies.
     * @param n number of shift operations
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return shifted result
     */
    public abstract AbstractInt shr(final AbstractInt n, final IntegerType intType);

    /**
     * Creates a new AbstractInt from the difference of two existing abstract
     * ints.
     * @param n value to be subtracted from this
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param subtrahendSmaller true if this > n holds.
     * @param subtrahendSmallerOrEqual true if this >= n holds.
     * @return difference between this instance and the argument
     */
    public final AbstractInt sub(
        final AbstractInt n,
        final boolean sameReference,
        final boolean subtrahendSmaller,
        final boolean subtrahendSmallerOrEqual,
        final IntegerType intType)
    {
        if (sameReference) {
            // Hah!
            return AbstractInt.getZero();
        }
        AbstractInt res = null;
        final AbstractInt negated = n.negate(IntegerType.UNBOUND);
        res = this.add(negated, intType);

        if (subtrahendSmaller && res.containsLiteral(0)) {
            res =
                AbstractInt.create(
                    IntervalBound.ONE,
                    res.getUpper(),
                    res.getMinLower(),
                    res.getMaxUpper(),
                    res.getLowerCounter(),
                    res.getUpperCounter());
        } else if (subtrahendSmallerOrEqual && res.containsLiteral(-1)) {
            res =
                AbstractInt.create(
                    IntervalBound.ZERO,
                    res.getUpper(),
                    res.getMinLower(),
                    res.getMaxUpper(),
                    res.getLowerCounter(),
                    res.getUpperCounter());
        }

        return res;
    }

    /**
     * Note that depending on the implementation, the result can contain more
     * than the union. Consider for example the AbstractInts representing 1 and
     * 3. The union will be a superset of {1,3}, but depending on the internal
     * representation it could be {1,2,3}. The counter will not be increased!
     * @param other another AbstractInt
     * @return an AbstractInt representing at least the union of all values
     * represented by the two given AbstractInts (this and o).
     */
    public abstract AbstractInt union(final AbstractInt other);

    /**
     * Creates a new AbstractInt by shifting the bits representing this instance
     * to the right as often as the argument specifies.
     * @param n number of shift operations
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return shifted result
     */
    public abstract AbstractInt ushr(final AbstractInt n, final IntegerType intType);

    /**
     * Creates a new AbstractInt by applying logical XOR to the two existing
     * AbstractInts.
     * @param n value to be XORed to this
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return logical XOR of this instance and the argument
     */
    public abstract AbstractInt xor(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType);

    /**
     * Add the comparison information from the other int to this
     * @param other some abstract int
     */
    void copyComparisonsFrom(final AbstractInt other) {
        for (final Pair<IntegerRelationType, BigInteger> comparison : other.wasComparedTo) {
            this.wasComparedTo.add(comparison);
        }
    }

}
