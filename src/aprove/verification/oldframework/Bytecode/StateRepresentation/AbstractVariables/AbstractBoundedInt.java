package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Parent class of all int/long value representations in our symbolic
 * interpretation.
 * @author Carsten Otto, Marc Brockschmidt, Jera Hensel
 */
public abstract class AbstractBoundedInt extends AbstractNumber {

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
     * Check if a compT b is true.
     * @param intRel an {@link IntArithmetic} comparison
     * @param a one AbstractBoundedInt
     * @param b another AbstractBoundedInt
     * @param sameRef true only if the two integers are referenced from the same
     * references
     * @param areDefinitelyUnequal true if the two integers cannot be the same
     * @return true only if a compT b holds. False may be returned if we do not
     * know the result.
     */
    public static boolean computeComparisonResult(
        final IntegerRelationType intRel,
        final AbstractBoundedInt a,
        final AbstractBoundedInt b,
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
     * @param literal the literal value of the created AbstractBoundedInt
     * @return a LiteralBoundedInt representing the given value
     */
    public static LiteralBoundedInt create(final BigInteger literal) {
        return LiteralBoundedInt.createLiteralInt(literal);
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
    public static AbstractBoundedInt create(
        final IntervalBound low,
        final IntervalBound up,
        final boolean containsZero,
        final IntervalBound minLow,
        final IntervalBound maxUp,
        final int newLowerCounter,
        final int newUpperCounter)
    {
        final AbstractBoundedInt res;
        if (low.equals(up)) {
            assert (!up.isZero() || containsZero);
            res = LiteralBoundedInt.createLiteralInt(up.getConstant());
        } else {
            res = new IntervalBoundedInt(low, up, containsZero, minLow, maxUp, newLowerCounter, newUpperCounter);
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
    public static AbstractBoundedInt create(
        final IntervalBound low,
        final IntervalBound up,
        final IntervalBound minLow,
        final IntervalBound maxUp,
        final int newLowerCounter,
        final int newUpperCounter)
    {
        final boolean containsZero = IntervalBoundedInt.containsZero(low, up);
        return AbstractBoundedInt.create(low, up, containsZero, minLow, maxUp, newLowerCounter, newUpperCounter);
    }

    /**
     * @param literal the literal value of the created AbstractBoundedInt
     * @return an abstract int representing the given value
     */
    public static LiteralBoundedInt create(final long literal) {
        return LiteralBoundedInt.createLiteralInt(literal);
    }

    /**
     * @return AI representing -1.
     */
    public static final LiteralBoundedInt getMOne() {
        return new LiteralBoundedInt(BigInteger.ONE.negate());
    }

    /**
     * @return AI representing 1
     */
    public static final LiteralBoundedInt getOne() {
        return new LiteralBoundedInt(BigInteger.ONE);
    }

    /**
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return AI representing an arbitrary value (with correct bounds, however)
     */
    public static IntervalBoundedInt getUnknown(final IntegerType intType) {
        return new IntervalBoundedInt(intType);
    }

    /**
     * @return AI representing 0.
     */
    public static final LiteralBoundedInt getZero() {
        return new LiteralBoundedInt(BigInteger.ZERO);
    }

    /**
     * Check if a compT b is decidable, i.e. we know that a compT b holds or a
     * invCompT b holds (where invCompT is the inverse of compT).
     * @param intRel an {@link IntArithmetic} comparison
     * @param a one AbstractBoundedBoundedInt
     * @param b another AbstractInt
     * @param sameRef true only if the two integers are referenced from the same
     * references
     * @param areUnequal true if the two integers cannot be the same
     * @return true if a compT b can be decided
     */
    public static boolean isDecidableComparison(
        final IntegerRelationType intRel,
        final AbstractBoundedInt a,
        final AbstractBoundedInt b,
        final boolean sameRef,
        final boolean areUnequal)
    {

        final IntegerRelationType intRelInv = intRel.invert();
        return (AbstractBoundedInt.computeComparisonResult(intRel, a, b, sameRef, areUnequal) || AbstractBoundedInt
            .computeComparisonResult(intRelInv, a, b, sameRef, areUnequal));
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

    /*
     * We have no idea where to go, but our current lower bound is smaller
     * than one of the minimal upper bound we had earlier. Try going to -inf.
     */
    private static AbstractBoundedInt widenLowerBoundToTypeMin(final IntegerType intType,
                                                        final AbstractNumberMergeResult result,
                                                        AbstractBoundedInt resultVar) {
        result.setEnforcedWideningCost(CostType.INTERVAL_INFINITE);
        return AbstractBoundedInt.create(
                                         intType.getLower(),
                                         resultVar.getUpper(),
                                         resultVar.containsLiteral(0),
                                         resultVar.getMinLower(),
                                         resultVar.getMaxUpper(),
                                         resultVar.getLowerCounter(),
                                         resultVar.getUpperCounter());
    }

    /*
     * We have no idea where to go, but our current upper bound is bigger
     * than one of the maximal upper bound we had earlier. Try going to +inf.
     */
    private static AbstractBoundedInt widenUpperBoundToTypeMax(final IntegerType intType,
                                                                 final AbstractNumberMergeResult result,
                                                                 AbstractBoundedInt resultVar) {
        result.setEnforcedWideningCost(CostType.INTERVAL_INFINITE);
        return AbstractBoundedInt.create(
                                         resultVar.getLower(),
                                         intType.getUpper(),
                                         resultVar.containsLiteral(0),
                                         resultVar.getMinLower(),
                                         resultVar.getMaxUpper(),
                                         resultVar.getLowerCounter(),
                                         resultVar.getUpperCounter());
    }

    /**
     * Comparisons performed with the encoded value, such that for every pair ($rel, $val) we checked $this $rel $val.
     * Here, $val is some constant.
     */
    private final Set<Pair<IntegerRelationType, BigInteger>> wasComparedTo = new LinkedHashSet<>();

    /**
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return AbstractBoundedInt representing all absolute values of values represented by this
     * @throws OverflowException if the value cannot be represented in intType (i.e. if it contains intType.getLower())
     */
    public abstract AbstractBoundedInt absolute(final IntegerType intType) throws OverflowException;

    /**
     * Creates a new AbstractBoundedInt from the sum of two existing AbstractBoundedInts.
     * @param n value to be added to this
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param handleOverflows true iff an overflow should be handled internally.
     * @return sum of this instance and the argument and inner bounds to keep lost information if an overflow occurs.
     * @throws OverflowException iff the addition might cause an overflow and {@code ignoreOverflowArgs == true}
     */
    public Triple<AbstractBoundedInt, BigInteger, BigInteger> add(
        final AbstractBoundedInt n,
        final IntegerType intType,
        final boolean handleOverflows
    ) throws OverflowException {
        return this.add(n, intType, handleOverflows, YNM.MAYBE, YNM.MAYBE);
    }

    /**
     * Creates a new AbstractBoundedInt from the sum of two existing AbstractBoundedInts.
     * @param n value to be added to this
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param handleOverflows true iff an overflow should be handled internally.
     * @param posOverflow NO if we can exclude positive overflows, YES if we have a positive overflow for sure.
     * @param negOverflow NO if we can exclude negative overflows, YES if we have a negative overflow for sure.
     * @return sum of this instance and the argument and inner bounds to keep lost information if an overflow occurs.
     * @throws OverflowException iff the addition might cause an overflow and {@code ignoreOverflowArgs == true}
     */
    public abstract Triple<AbstractBoundedInt, BigInteger, BigInteger> add(
        final AbstractBoundedInt n,
        final IntegerType intType,
        final boolean handleOverflows,
        final YNM posOverflow,
        final YNM negOverflow
    ) throws OverflowException;

    /**
     * Pushes an AbstractBoundedInt back into its bounds.
     * @param intType The type of this.
     * @return A valid AbstractBoundedInt that can be represented by its type and inner bounds, if otherwise we would
     * lose some information.
     */
    public Triple<AbstractBoundedInt, BigInteger, BigInteger> adjustToBounds(final IntegerType intType) {
        return this.adjustToBounds(intType, YNM.MAYBE, YNM.MAYBE);
    }

    /**
     * Pushes an AbstractBoundedInt back into its bounds.
     * @param intType The type of this.
     * @param posOverflow NO if we can exclude positive overflows, YES if we have a positive overflow for sure.
     * @param negOverflow NO if we can exclude negative overflows, YES if we have a negative overflow for sure.
     * @return A valid AbstractBoundedInt that can be represented by its type and inner bounds, if otherwise we would
     * lose some information.
     */
    public abstract Triple<AbstractBoundedInt, BigInteger, BigInteger> adjustToBounds(
        final IntegerType intType,
        final YNM posOverflow,
        final YNM negOverflow
    );

    /**
     * Creates a new AbstractBoundedInt by applying logical AND to the two existing
     * AbstractBoundedInts.
     * @param n value to be ANDed to this
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param sameReference true iff both operands are the very same value.
     * @param ignoreOverflows if true, use infinity values when needed
     * @return logical AND of this instance and the argument
     */
    public abstract AbstractBoundedInt and(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        boolean ignoreOverflows
    );

    /**
     * Try to compare to given AbstractBoundedInt to this. For -1, 0, 1 this
     * corresponds to compareTo. For null we do not know the result. In most
     * cases you should make use of "computeComparisonResult" which may give
     * positive answers for some relations even if the comparison cannot be
     * decided.
     * @param other compare to this AbstractBoundedInt
     * @return -1, 0, 1 or null.
     */
    public abstract Integer compareToApprox(AbstractBoundedInt other);

    /**
     * @param other another AI
     * @return true iff other is contained in the interval specified by this
     */
    public abstract boolean containsInt(final AbstractBoundedInt other);

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
     * Creates a new AbstractBoundedInt by dividing all values from this by all values
     * from the argument using integer division (rounding towards zero).
     * @param n value to be used as divisor
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param handleOverflows true iff an overflow should be handled internally.
     * @return AbstractBoundedInt obtained by dividing values from this AbstractBoundedInt by values from n. If n can
     *         be 0, the first boolean value is set to true and indicates a possible ArithmeticException. If n is equal
     *         to 0 the returned AbstractBoundedInt is null and only the exception must be thrown (the first boolean
     *         value is still set to true). If the result represents values which are obtained by rounding towards zero
     *         (i.e., they do not correspond to exact division on real numbers), the second boolean value is set to
     *         true.
     * @throws OverflowException iff the result cannot be represented using <code>intType</code>
     */
    public Triple<? extends AbstractBoundedInt, Boolean, Boolean> div(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean handleOverflows) throws OverflowException
    {
        //If we only have a division by zero, do a shortcut here:
        if (n.isZero()) {
            return new Triple<AbstractBoundedInt, Boolean, Boolean>(null, Boolean.TRUE, Boolean.FALSE);
        }
        AbstractBoundedInt res = null;
        final boolean nContainsZero = n.containsLiteral(0);
        final boolean rounded;
        // first, some special cases
        if (sameReference) {
            // a/a = 1:
            res = AbstractBoundedInt.getOne();
            rounded = false;
        } else if (n.isOne()) {
            // Division by 1
            res = this;
            rounded = false;
        } else if (n.isNegOne()) {
            // Division by -1
            try {
                res = this.negate(intType);
                rounded = false;
            } catch (final OverflowException e) {
                res = e.getValue(true);
                throw new OverflowException(intType, ArithmeticOperationType.TIDIV, res);
            }
        } else {
            // Now, do the exact computation
            final AbstractBoundedInt thisAbs = this.absolute(IntegerType.UNBOUND);
            final AbstractBoundedInt thatAbs = n.absolute(IntegerType.UNBOUND).removeZeroFromInteger();
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
                AbstractBoundedInt.create(
                    resMin,
                    resMax,
                    this.getMinLower(),
                    this.getMaxUpper(),
                    newLowerCounter,
                    newUpperCounter);
            if (!intType.canRepresent(res)) {
                throw new OverflowException(intType, ArithmeticOperationType.TIDIV, res);
            }
            // assuming that rounding occurs is sound and will be true in almost every case (for literals, this method
            // is overridden)
            rounded = true;
        }
        return new Triple<AbstractBoundedInt, Boolean, Boolean>(res, nContainsZero, rounded);
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
     * @return the literal value of this AbstractBoundedInt (if it exists)
     */
    public abstract BigInteger getLiteral();

    /**
     * @return the smallest number represented by this AbstractBoundedInt (may be
     * -infty)
     */
    public abstract IntervalBound getLower();

    /**
     * @return how often this integer was widened towards the lower bound during
     * abstraction.
     */
    public abstract int getLowerCounter();

    /**
     * @return the biggest number ever represented by this AbstractBoundedInt
     * in its arithmetic history (may be -infty)
     */
    public abstract IntervalBound getMaxUpper();

    /**
     * @return the smallest number ever represented by this AbstractBoundedInt
     * in its arithmetic history (may be -infty)
     */
    public abstract IntervalBound getMinLower();

    /**
     * @return the largest number represented by this AbstractBoundedInt (may be
     * +infty)
     */
    public abstract IntervalBound getUpper();

    /**
     * @return how often this integer was widened towards the upper bound during
     * abstraction.
     */
    public abstract int getUpperCounter();

    /**
     * @return True if all values represented by this AbstractBoundedInt are bigger than one (&gt;1)
     */
    public abstract boolean isBiggerOne();

    public boolean isConstrained() {
        return this.getLower().isFinite() || this.getUpper().isFinite() || this.isNonZero();
    }

    /**
     * @return true if all values represented by this AbstractBoundedInt are negative
     * (&lt;0)
     */
    public abstract boolean isNegative();

    /**
     * @return if this AbstractBoundedInt represents -1
     */
    public abstract boolean isNegOne();

    /**
     * @return true if all values represented by this AbstractBoundedInt are
     * non-negative (&ge;0)
     */
    public abstract boolean isNonNegative();

    /**
     * @return true if all values represented by this AbstractBoundedInt are
     * non-negative (&le;0)
     */
    public abstract boolean isNonPositive();

    /**
     * @return if this AbstractBoundedInt does not contain 0
     */
    public abstract boolean isNonZero();

    /**
     * @return if this AbstractBoundedInt represents 1
     */
    public abstract boolean isOne();

    /**
     * @return true if all values represented by this AbstractBoundedInt are positive
     * (&gt;0)
     */
    public abstract boolean isPositive();

    /**
     * @return True if all values represented by this AbstractBoundedInt are smaller than minus one (&lt;-1)
     */
    public abstract boolean isSmallerMinusOne();

    /**
     * @return if this AbstractBoundedInt represents 0
     */
    public abstract boolean isZero();

    public boolean mayIntersect( AbstractBoundedInt b){
        AbstractBoundedInt value_intersection;
        try {
            value_intersection = this.intersect(b).getThisAsAbstractBoundedInt();
        } catch (IntersectionFailException e) {
            return true;
        }
        return value_intersection.getLower().compareTo(value_intersection.getUpper()) == 1;
    }

    public AbstractNumberMergeResult merge(final AbstractNumber otherVar, final boolean increaseCounters, final IntegerType intType) {
    	return merge(otherVar, increaseCounters, intType, COUNTER_MAX);
    }
    
    /**
     * Merge the values represented by this {@link AbstractBoundedInt} with another one.
     * @param newVar the {@link AbstractBoundedInt} to merge with
     * @return an {@link AbstractNumberMergeResult}, holding an
     * {@link AbstractVariable} that represents all values that are represented
     * by this and otherVar, costs to obtain this merged result and pointers to
     * the original variables.
     * 
     * @param mergeToExtremeValCountThreshold After how many simple merges do we need to introduce smallest/largest possible value?
     */
    public AbstractNumberMergeResult merge(
        final AbstractNumber newVar,
        final boolean increaseCounters,
        final IntegerType intType,
        final int mergeToExtremeValCountThreshold
        
    ) {
        if (this.equalsOnlyRepresentedValues(newVar)) {
            final AbstractNumberMergeResult r = new AbstractNumberMergeResult(this, newVar);
            r.setMergedVariable(this);
            r.setVarAtoMerged(CostType.NONE);
            r.setVarBtoMerged(CostType.NONE);
            return r;
        }

        if (!(newVar instanceof AbstractBoundedInt)) {
            throw new IllegalArgumentException("Parameter needs to be " + "AbstractBoundedInt");
        }
        final AbstractBoundedInt newInt = (AbstractBoundedInt) newVar;

        // If the other is not this the result will be the union.
        final AbstractNumberMergeResult result = new AbstractNumberMergeResult(this, newInt);

        AbstractBoundedInt resultVar = this.union(newInt);

        this.computeCosts(newInt, resultVar, result);
        if(increaseCounters){
            resultVar = this.increaseCounter(newInt, resultVar);
        }

        resultVar = this.generalizeUpperBound(intType, newInt, result, mergeToExtremeValCountThreshold, resultVar);

        resultVar = this.generalizeLowerBound(intType, newInt, result, mergeToExtremeValCountThreshold, resultVar);

        if (intType == IntegerType.UNBOUND_POSITIVE) {
            resultVar = resultVar.onlyPositive();
        } else if (intType == IntegerType.UNBOUND_NON_NEGATIVE) {
            resultVar = resultVar.onlyNonNegative();
        }
        result.setMergedVariable(resultVar);
        return result;
    }

    /**
     * Creates a new AbstractBoundedInt with all possible remainders of a modulo b, where a is in this interval and b in
     * the AbstractBoundedInt passed as argument.
     * Warning: This method works fine for analyzing JBC and LLVM, but be aware of the fact that different remainder
     * implementations are out there when using this method for analyzing something else!
     * @param n value to be multiplied
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param handleOverflows true iff an overflow should be handled internally.
     * @return AbstractBoundedInt of values obtained by modulo operations between this
     * and the values from n. If b can be 0, the boolean value is set to true
     * and indicates a possible ArithmeticException. If b is equal to 0 the
     * returned AbstractBoundedInt is null and only the exception must be thrown.
     */
    public Pair<? extends AbstractBoundedInt, Boolean> mod(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean handleOverflows
    ) {
        final boolean oContainsZero = n.containsLiteral(0);
        // The divisor should not be negative (no use for that yet, could be adapted later):
        if (!n.isNonNegative()) {
            return new Pair<>(AbstractBoundedInt.getUnknown(intType), oContainsZero);
        }
        // If we only have a division by zero, do a shortcut here:
        if (n.isZero()) {
            return new Pair<>(null, Boolean.TRUE);
        }
        // If this == 0, we know the result:
        if (this.isZero()) {
            return new Pair<>(AbstractBoundedInt.getZero(), oContainsZero);
        }
        if (sameReference) {
            // a % a = 0
            return new Pair<>(AbstractBoundedInt.getZero(), oContainsZero);
        }
        if (n.isOne()) {
            // a % 1 = 0
            return new Pair<>(AbstractBoundedInt.getZero(), Boolean.FALSE);
        }
        // Compute the exact values (will not throw an exception). We know that n is nonnegative here.
        try {
            /*
             * If x and y are both positive, we have x mod y = x rem y.
             * We know: x rem y = x - ((x/y) * y) = x + (-((x/y) * y)) = x + ((x/y) * (-y)).
             * If x is negative, we have x mod y = x + ((x/y) * (-y)) + y.
             */
            // Divide the interval into non-positive and non-negative intervals:
            final AbstractBoundedInt lowerInterval;
            final AbstractBoundedInt upperInterval;
            if (this.getLower().isNonNegative()) {
                // the whole interval is non-negative
                lowerInterval = null;
                upperInterval = this;
            } else {
                if (this.getUpper().isNonPositive()) {
                    // the whole interval is non-positive
                    lowerInterval = this;
                    upperInterval = null;
                } else {
                    // the interval is mixed positive and negative, so we need to divide it
                    lowerInterval =
                        AbstractBoundedInt.create(
                            this.getLower(),
                            IntervalBound.ZERO,
                            true,
                            this.getMinLower(),
                            this.getMaxUpper(),
                            this.getLowerCounter(),
                            this.getUpperCounter()
                        );
                    upperInterval =
                        AbstractBoundedInt.create(
                            IntervalBound.ZERO,
                            this.getUpper(),
                            true,
                            this.getMinLower(),
                            this.getMaxUpper(),
                            this.getLowerCounter(),
                            this.getUpperCounter()
                        );
                }
            }
            // Compute the resulting intervals individually:
            AbstractBoundedInt lowerRes = null;
            AbstractBoundedInt upperRes = null;
            if (lowerInterval != null) {
                final Triple<? extends AbstractBoundedInt, Boolean, Boolean> xDivY =
                    lowerInterval.div(n, sameReference, IntegerType.UNBOUND, handleOverflows);
                assert (xDivY.y.equals(Boolean.valueOf(oContainsZero)));
                final AbstractBoundedInt yNeg = n.negate(IntegerType.UNBOUND);
                final AbstractBoundedInt xDivYTimesYNeg = xDivY.x.mul(yNeg, IntegerType.UNBOUND, handleOverflows).x;
                final AbstractBoundedInt xDivYTimesYNegPlusY =
                    xDivYTimesYNeg.add(n, IntegerType.UNBOUND, handleOverflows).x;
                lowerRes = xDivYTimesYNegPlusY.add(lowerInterval, IntegerType.UNBOUND, handleOverflows).x;
            }
            if (upperInterval != null) {
                final Triple<? extends AbstractBoundedInt, Boolean, Boolean> xDivY =
                    upperInterval.div(n, sameReference, IntegerType.UNBOUND, handleOverflows);
                assert (xDivY.y.equals(Boolean.valueOf(oContainsZero)));
                final AbstractBoundedInt yNeg = n.negate(IntegerType.UNBOUND);
                final AbstractBoundedInt xDivYTimesYNeg = xDivY.x.mul(yNeg, IntegerType.UNBOUND, handleOverflows).x;
                upperRes = xDivYTimesYNeg.add(upperInterval, IntegerType.UNBOUND, handleOverflows).x;
            }
            // Now join the intervals:
            final AbstractBoundedInt mid;
            if (lowerRes != null) {
                if (upperRes != null) {
                    mid = lowerRes.union(upperRes);
                } else {
                    mid = lowerRes;
                }
            } else {
                mid = upperRes;
            }
            final int newLowerCounter = Math.max(this.getLowerCounter(), n.getLowerCounter());
            final int newUpperCounter = Math.max(this.getUpperCounter(), n.getUpperCounter());
            AbstractBoundedInt res =
                AbstractBoundedInt.create(
                    mid.getLower(),
                    mid.getUpper(),
                    this.getMinLower(),
                    this.getMaxUpper(),
                    newLowerCounter,
                    newUpperCounter
                );
            if (!intType.canRepresent(res)) {
                if (handleOverflows) {
                    res = res.adjustToBounds(intType).x;
                } else {
                    //TODO: Shouldn't we throw an exception here?
                    return new Pair<>(AbstractBoundedInt.getUnknown(intType), oContainsZero);
                }
            }
            return new Pair<>(res, oContainsZero);
        } catch (final OverflowException o) {
            assert (false) : "Overflow occurred when only computing with unbounded integers!";
            return null;
        }
    }

    /**
     * Creates an AbstractBoundedInt by multiplying all values from this by all values
     * from the argument.
     * @param n value to be multiplied
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param handleOverflows true iff an overflow should be handled internally.
     * @return AbstractBoundedInt of values obtained by multiplying values from this AbstractBoundedInt with values
     *  from n and inner bounds to keep lost information if an overflow occurs.
     * @throws OverflowException iff overflows should not be ignored and the operation might cause an overflow
     */
    public Triple<AbstractBoundedInt, BigInteger, BigInteger> mul(
        final AbstractBoundedInt n,
        final IntegerType intType,
        final boolean handleOverflows
    ) throws OverflowException {
        return this.mul(n,  intType,  handleOverflows, YNM.MAYBE, YNM.MAYBE);
    }

    /**
     * Creates an AbstractBoundedInt by multiplying all values from this by all values
     * from the argument.
     * @param n value to be multiplied
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param handleOverflows true iff an overflow should be handled internally.
     * @param posOverflow NO if we can exclude positive overflows, YES if we have a positive overflow for sure.
     * @param negOverflow NO if we can exclude negative overflows, YES if we have a negative overflow for sure.
     * @return AbstractBoundedInt of values obtained by multiplying values from this AbstractBoundedInt with values
     *  from n and inner bounds to keep lost information if an overflow occurs.
     * @throws OverflowException iff overflows should not be ignored and the operation might cause an overflow
     */
    public abstract Triple<AbstractBoundedInt, BigInteger, BigInteger> mul(
        final AbstractBoundedInt n,
        final IntegerType intType,
        final boolean handleOverflows,
        final YNM posOverflow,
        final YNM negOverflow
    ) throws OverflowException;

    /**
     * Creates an AbstractBoundedInt by negating all values in this AbstractBoundedInt.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @return negated AbstractBoundedInt
     * @throws OverflowException iff overflows should not be ignored and the operation might cause an overflow
     */
    public abstract AbstractBoundedInt negate(final IntegerType intType) throws OverflowException;

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
     * @return an AbstractBoundedInt that only contains the negative values of this
     */
    public AbstractBoundedInt onlyNegative() {
        assert (!this.isNonNegative());
        return AbstractBoundedInt.create(
            this.getLower(),
            this.getUpper().min(IntervalBound.NEGONE),
            false,
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());
    }

    /**
     * @return an AbstractBoundedInt that only contains the nonnegative values of this
     */
    public AbstractBoundedInt onlyNonNegative() {
        assert (!this.isNegative());
        return AbstractBoundedInt.create(
            this.getLower().max(IntervalBound.ZERO),
            this.getUpper(),
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());

    }

    /**
     * @return an AbstractBoundedInt that only contains the non-positive values of this
     */
    public AbstractBoundedInt onlyNonPositive() {
        assert (!this.isPositive());
        return AbstractBoundedInt.create(
            this.getLower(),
            this.getUpper().min(IntervalBound.ZERO),
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());

    }

    /**
     * @return an AbstractBoundedInt that only contains the positive values of this
     */
    public AbstractBoundedInt onlyPositive() {
        assert (!this.isNonPositive());
        return AbstractBoundedInt.create(
            this.getLower().max(IntervalBound.ONE),
            this.getUpper(),
            false,
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());
    }

    /**
     * Creates a new AbstractBoundedInt by applying logical OR to the two existing
     * AbstractBoundedInts.
     * @param n value to be ORed to this
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param ignoreOverflows if true, use infinity values when needed
     * @return logical OR of this instance and the argument
     */
    public abstract AbstractBoundedInt or(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        boolean ignoreOverflows
    );

    /**
     * Creates a new AbstractBoundedInt with all possible remainders of a modulo b, where a is in this interval and b in
     * the AbstractBoundedInt passed as argument.
     * Warning: This method works fine for analyzing JBC and LLVM, but be aware of the fact that different remainder
     * implementations are out there when using this method for analyzing something else!
     * @param n value to be multiplied
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param handleOverflows true iff an overflow should not be handled internally.
     * @return AbstractBoundedInt of values obtained by modulo operations between this
     * and the values from n. If b can be 0, the boolean value is set to true
     * and indicates a possible ArithmeticException. If b is equal to 0 the
     * returned AbstractBoundedInt is null and only the exception must be thrown.
     */
    public Pair<? extends AbstractBoundedInt, Boolean> rem(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean handleOverflows
    ) {
        // If we only have a division by zero, do a shortcut here:
        if (n.isZero()) {
            return new Pair<>(null, Boolean.TRUE);
        }

        final boolean oContainsZero = n.containsLiteral(0);
        // If this == 0, we know the result:
        if (this.isZero()) {
            return new Pair<>(AbstractBoundedInt.getZero(), oContainsZero);
        }

        if (sameReference) {
            // a % a = 0
            return new Pair<>(AbstractBoundedInt.getZero(), oContainsZero);
        }
        if (n.isOne()) {
            // a % 1 = 0
            return new Pair<>(AbstractBoundedInt.getZero(), Boolean.FALSE);
        }

        // x%y = x - ((x/y) * y) = x + (-((x/y) * y)) = x + ((x/y) * (-y))
        // Compute the exact values (will not throw an exception):
        try {
            final Triple<? extends AbstractBoundedInt, Boolean, Boolean> xDivY =
                this.div(n, sameReference, IntegerType.UNBOUND, handleOverflows);
            assert (xDivY.y.equals(Boolean.valueOf(oContainsZero)));

            final AbstractBoundedInt yNeg = n.negate(IntegerType.UNBOUND);

            final AbstractBoundedInt xDivYTimesYNeg = xDivY.x.mul(yNeg, IntegerType.UNBOUND, handleOverflows).x;

            final AbstractBoundedInt mid = xDivYTimesYNeg.add(this, IntegerType.UNBOUND, handleOverflows).x;

            /*
             * [...] the result of the remainder operation can be negative only if
             * the dividend is negative and can be positive only if the dividend is
             * positive.
             *  -- JVMS, documentation of the irem opcode
             */
            IntervalBound resLow = mid.getLower().max(n.getUpper().abs().negate().add(IntervalBound.ONE));
            IntervalBound resUp = mid.getUpper().min(n.getUpper().abs().add(IntervalBound.NEGONE));
            if (this.isNonNegative()) {
                resLow = resLow.max(IntervalBound.ZERO);
            } else if (this.isNonPositive()) {
                resUp = resUp.min(IntervalBound.ZERO);
            }

            final int newLowerCounter = Math.max(this.getLowerCounter(), n.getLowerCounter());
            final int newUpperCounter = Math.max(this.getUpperCounter(), n.getUpperCounter());

            final AbstractBoundedInt res =
                AbstractBoundedInt.create(
                    resLow,
                    resUp,
                    this.getMinLower(),
                    this.getMaxUpper(),
                    newLowerCounter,
                    newUpperCounter);

            if (!intType.canRepresent(res)) {
                //TODO: Shouldn't we throw an exception here?
                return new Pair<>(AbstractBoundedInt.getUnknown(intType), oContainsZero);
            }

            return new Pair<>(res, oContainsZero);
        } catch (final OverflowException o) {
            assert (false) : "Overflow occurred when only computing with unbounded integers!";
            return null;
        }
    }

    /**
     * Remove zero from this.
     * @return a possibly modified AbstractBoundedInt
     */
    public abstract AbstractBoundedInt removeZeroFromInteger();

    /**
     * @return True if both lower and upper bounds of this AbstractBoundedInt are finite (i.e., it represents only
     *         finitely many numbers). False otherwise.
     */
    public boolean representsFinitelyManyNumbers() {
        return this.getLower().isFinite() && this.getUpper().isFinite();
    }

    /**
     * @param newLow The new lower bound.
     * @return An AbstractBoundedInt with its lower bound set to the specified bound and everything else as in the
     *         current AbstractBoundedInt if the new lower bound is consistent with (i.e., <=) the upper bound.
     *         Null otherwise.
     */
    public AbstractBoundedInt setLower(final IntervalBound newLow) {
        if (newLow.compareTo(this.getUpper()) > 0) {
            return null;
        }
        return AbstractBoundedInt.create(
            newLow,
            this.getUpper(),
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());
    }

    /**
     * @param newUp The new upper bound.
     * @return An AbstractBoundedInt with its upper bound set to the specified bound and everything else as in the
     *         current AbstractBoundedInt if the new upper bound is consistent with (i.e., >=) the lower bound.
     *         Null otherwise.
     */
    public AbstractBoundedInt setUpper(final IntervalBound newUp) {
        if (newUp.compareTo(this.getLower()) < 0) {
            return null;
        }
        return AbstractBoundedInt.create(
            this.getLower(),
            newUp,
            this.getMinLower(),
            this.getMaxUpper(),
            this.getLowerCounter(),
            this.getUpperCounter());
    }

    /**
     * Creates a new AbstractBoundedInt by shifting the bits representing this instance
     * to the left as often as the argument specifies.
     * @param n number of shift operations
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param ignoreOverflows if true, use infinity values when needed
     * @return shifted result
     */
    public abstract AbstractBoundedInt shl(final AbstractBoundedInt n, final IntegerType intType, boolean ignoreOverflows);

    /**
     * Creates a new AbstractBoundedInt by shifting the bits representing this instance
     * to the right as often as the argument specifies.
     * @param n number of shift operations
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param ignoreOverflows if true, use infinity values when needed
     * @return shifted result
     */
    public abstract AbstractBoundedInt shr(final AbstractBoundedInt n, final IntegerType intType, boolean ignoreOverflows);

    /**
     * Creates a new AbstractBoundedInt from the difference of two existing abstract ints.
     * @param n value to be subtracted from this
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param subtrahendSmaller true if this > n holds.
     * @param subtrahendSmallerOrEqual true if this >= n holds.
     * @param handleOverflows true iff an overflow should be handled internally.
     * @param excludePositiveOverflows true iff we can exclude positive overflows.
     * @param excludeNegativeOverflows true iff we can exclude negative overflows.
     * @return difference between this instance and the argument and inner bounds to keep lost information if an
     * overflow occurs.
     * @throws OverflowException iff this operation might cause an overflow
     */
    public final Triple<AbstractBoundedInt, BigInteger, BigInteger> sub(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final boolean subtrahendSmaller,
        final boolean subtrahendSmallerOrEqual,
        final IntegerType intType,
        final boolean handleOverflows) throws OverflowException
    {
        return
            this.sub(
                n,
                sameReference,
                subtrahendSmaller,
                subtrahendSmallerOrEqual,
                intType,
                handleOverflows,
                YNM.MAYBE,
                YNM.MAYBE
            );
    }

    /**
     * Creates a new AbstractBoundedInt from the difference of two existing abstract ints.
     * @param n value to be subtracted from this
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param subtrahendSmaller true if this > n holds.
     * @param subtrahendSmallerOrEqual true if this >= n holds.
     * @param handleOverflows true iff an overflow should be handled internally.
     * @param posOverflow NO if we can exclude positive overflows, YES if we have a positive overflow for sure.
     * @param negOverflow NO if we can exclude negative overflows, YES if we have a negative overflow for sure.
     * @return difference between this instance and the argument and inner bounds to keep lost information if an
     * overflow occurs.
     * @throws OverflowException iff this operation might cause an overflow
     */
    public final Triple<AbstractBoundedInt, BigInteger, BigInteger> sub(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final boolean subtrahendSmaller,
        final boolean subtrahendSmallerOrEqual,
        final IntegerType intType,
        final boolean handleOverflows,
        final YNM posOverflow,
        final YNM negOverflow) throws OverflowException
    {
        boolean overflow = false;
        if (sameReference) {
            // Hah!
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(AbstractBoundedInt.getZero(), null, null);
        }
        Triple<AbstractBoundedInt, BigInteger, BigInteger> res = null;
        AbstractBoundedInt resInt = null;
        try {
            final AbstractBoundedInt negated = n.negate(IntegerType.UNBOUND);
            res = this.add(negated, intType, handleOverflows, posOverflow, negOverflow);
            resInt = res.x;
        } catch (final OverflowException e) {
            // This should only occur if we do not handle overflows.
            if (Globals.useAssertions) {
                assert (!handleOverflows) : "Overflow could not be handled in addition.";
            }
            resInt = e.getValue(true);
            overflow = true;
        }

        if (res.y == null) {
            // We do not have a handled overflow.
            if (subtrahendSmaller && resInt.containsLiteral(0)) {
                resInt =
                    AbstractBoundedInt.create(
                        IntervalBound.ONE,
                        resInt.getUpper(),
                        resInt.getMinLower(),
                        resInt.getMaxUpper(),
                        resInt.getLowerCounter(),
                        resInt.getUpperCounter());
            } else if (subtrahendSmallerOrEqual && resInt.containsLiteral(-1)) {
                resInt =
                    AbstractBoundedInt.create(
                        IntervalBound.ZERO,
                        resInt.getUpper(),
                        resInt.getMinLower(),
                        resInt.getMaxUpper(),
                        resInt.getLowerCounter(),
                        resInt.getUpperCounter());
            }
        }
        if (overflow) {
            throw new OverflowException(intType, ArithmeticOperationType.SUB, resInt);
        }

        return res;
    }

    /**
     * @return scales this int down to a subset of [Byte.MIN_VALUE, Byte.MAX_VALUE], preserving the bounds if possible
     * @throws OverflowException iff the cast results in a loss of precision
     */
    public abstract AbstractBoundedInt toByteValue() throws OverflowException;

    /**
     * @return scales this int down to a subset of [Character.MIN_VALUE, Character.MAX_VALUE], preserving the bounds if
     * possible
     * @throws OverflowException iff the cast results in a loss of precision
     */
    public abstract AbstractBoundedInt toCharValue() throws OverflowException;

    /**
     * @return scales this int down to a subset of [Integer.MIN_VALUE, Integer.MAX_VALUE], preserving the bounds if possible
     * @throws OverflowException iff the cast results in a loss of precision
     */
    public abstract AbstractBoundedInt toIntegerValue() throws OverflowException;

    @Override
    public Collection<String> toSExpStrings(final AbstractVariableReference ref) {
    	throw new NotYetImplementedException("SExp export for bounded ints not implemented yet.");
    }

    /**
     * @return scales this int down to a subset of [Short.MIN_VALUE, Short.MAX_VALUE], preserving the bounds if possible
     * @throws OverflowException iff the cast results in a loss of precision
     */
    public abstract AbstractBoundedInt toShortValue() throws OverflowException;

    /**
     * Convenience method.
     * @param operandType cast to this type
     * @return an int value truncated to the given type
     * @throws OverflowException if an overflow occurs
     */
    public AbstractBoundedInt toValue(final OperandType operandType) throws OverflowException {
        switch (operandType) {
        case BYTE:
            return this.toByteValue();
        case CHAR:
            return this.toCharValue();
        case INTEGER:
            return this.toIntegerValue();
        case SHORT:
            return this.toShortValue();
        case VOID:
        case BOOLEAN:
        case ADDRESS:
        case ARRAY:
        case DOUBLE:
        case FLOAT:
        case LONG:
        case RETURN_ADDRESS:
        default:
            assert (false);
            return null;
        }
    }

    /**
     * Note that depending on the implementation, the result can contain more
     * than the union. Consider for example the AbstractBoundedInts representing 1 and
     * 3. The union will be a superset of {1,3}, but depending on the internal
     * representation it could be {1,2,3}. The counter will not be increased!
     * @param other another AbstractBoundedInt
     * @return an AbstractBoundedInt representing at least the union of all values
     * represented by the two given AbstractBoundedInts (this and o).
     */
    public abstract AbstractBoundedInt union(final AbstractBoundedInt other);

    /**
     * Creates a new AbstractBoundedInt with all possible remainders of a urem b for unsigned division, where a is in
     * this interval and b in the AbstractBoundedInt passed as argument.
     * @param n value to be multiplied
     * @param sameReference true iff both operands are the very same value.
     * @param intType the integer type of the operands and of the result.
     * @param handleOverflows true iff an overflow should not be handled internally.
     * @return AbstractBoundedInt of values obtained by unsigned modulo operations between this and the values from n.
     * If b can be 0, the boolean value is set to true and indicates a possible ArithmeticException. If b is equal to 0
     * the returned AbstractBoundedInt is null and only the exception must be thrown.
     */
    public Pair<? extends AbstractBoundedInt, Boolean> urem(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean handleOverflows)
    {
        // If we only have a division by zero, do a shortcut here:
        if (n.isZero()) {
            return new Pair<>(null, Boolean.TRUE);
        }

        final boolean oContainsZero = n.containsLiteral(0);

        final int newLowerCounter = Math.max(this.getLowerCounter(), n.getLowerCounter());
        final int newUpperCounter = Math.max(this.getUpperCounter(), n.getUpperCounter());

        // If this == 0, we know the result:
        if (this.isZero()) {
            return new Pair<>(AbstractBoundedInt.getZero(), oContainsZero);
        }

        if (sameReference) {
            // a urem a = 0
            return new Pair<>(AbstractBoundedInt.getZero(), oContainsZero);
        }
        if (n.isOne()) {
            // a urem 1 = 0
            return new Pair<>(AbstractBoundedInt.getZero(), Boolean.FALSE);
        }

        // if this may be negative, for most cases we do not (yet) compute the most precise result
        if (!this.isNonNegative()) {
            if (n.isPositive()) {

                // if this is negative and n is a positive constant, we compute the precise result
                if (n.isIntLiteral() && this.isNegative() && handleOverflows) {

                    BigInteger lower = this.getLower().getConstant();
                    BigInteger upper = this.getLower().getConstant();

                    if (upper.subtract(lower).compareTo(n.getIntLiteralValue()) < 0) {

                        // interpret lower and upper bound as unsigned value
                        BigInteger unsignedLower = lower.add(BigInteger.valueOf(2).pow(intType.getBitSize()));
                        BigInteger unsignedUpper = upper.add(BigInteger.valueOf(2).pow(intType.getBitSize()));

                        // compute new bounds
                        IntervalBound newLower = IntervalBound.create(unsignedLower.mod(n.getIntLiteralValue()));
                        IntervalBound newUpper = IntervalBound.create(unsignedUpper.mod(n.getIntLiteralValue()));

                        // if newLower <= newUpper, we have a valid interval (since we already know upper - lower < n)
                        if (newLower.compareTo(newUpper) <= 0) {
                            final AbstractBoundedInt res =
                                AbstractBoundedInt.create(
                                    newLower,
                                    newUpper,
                                    this.getMinLower(),
                                    this.getMaxUpper(),
                                    newLowerCounter,
                                    newUpperCounter);
                            return new Pair<>(res, oContainsZero);
                        }
                        // else fall through; not a valid interval
                    }
                    // else fall through; the interval of this is larger than n, so the result may be any value
                }

                // if n is positive but not a constant, we return [0, maxOfN - 1]
                final AbstractBoundedInt res =
                    AbstractBoundedInt.create(
                        IntervalBound.ZERO,
                        n.getUpper().add(IntervalBound.NEGONE),
                        this.getMinLower(),
                        this.getMaxUpper(),
                        newLowerCounter,
                        newUpperCounter);
                return new Pair<>(res, oContainsZero);
            }

            // else we just return the whole type interval
            return new Pair<>(AbstractBoundedInt.getUnknown(intType), oContainsZero);
        }

        // if this >= 0, x urem y = x rem y = x - ((x/y) * y) = x + (-((x/y) * y)) = x + ((x/y) * (-y))
        // Compute the exact values (will not throw an exception):
        try {
            final Triple<? extends AbstractBoundedInt, Boolean, Boolean> xDivY =
                this.div(n, sameReference, IntegerType.UNBOUND, handleOverflows);
            assert (xDivY.y.equals(Boolean.valueOf(oContainsZero)));

            final AbstractBoundedInt yNeg = n.negate(IntegerType.UNBOUND);

            final AbstractBoundedInt xDivYTimesYNeg = xDivY.x.mul(yNeg, IntegerType.UNBOUND, handleOverflows).x;

            final AbstractBoundedInt mid = xDivYTimesYNeg.add(this, IntegerType.UNBOUND, handleOverflows).x;

            IntervalBound resLow = mid.getLower().max(IntervalBound.ZERO);
            IntervalBound resUp = mid.getUpper().min(n.getUpper().abs().add(IntervalBound.NEGONE));

            final AbstractBoundedInt res =
                AbstractBoundedInt.create(
                    resLow,
                    resUp,
                    this.getMinLower(),
                    this.getMaxUpper(),
                    newLowerCounter,
                    newUpperCounter);

            if (!intType.canRepresent(res)) {
                //TODO: Shouldn't we throw an exception here?
                return new Pair<>(AbstractBoundedInt.getUnknown(intType), oContainsZero);
            }

            return new Pair<>(res, oContainsZero);
        } catch (final OverflowException o) {
            assert (false) : "Overflow occurred when only computing with unbounded integers!";
            return null;
        }
    }

    /**
     * Creates a new AbstractBoundedInt by shifting the bits representing this instance
     * to the right as often as the argument specifies.
     * @param n number of shift operations
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param ignoreOverflows if true, use infinity values when needed
     * @return shifted result
     */
    public abstract AbstractBoundedInt ushr(final AbstractBoundedInt n, final IntegerType intType, boolean ignoreOverflows);

    /**
     * Creates a new AbstractBoundedInt by applying logical XOR to the two existing
     * AbstractBoundedInts.
     * @param n value to be XORed to this
     * @param sameReference true iff both operands are the very same value.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     * @param ignoreOverflows if true, use infinity values when needed
     * @return logical XOR of this instance and the argument
     */
    public abstract AbstractBoundedInt xor(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        boolean ignoreOverflows);

    /**
     * Add the comparison information from the other int to this
     * @param other some abstract int
     */
    void copyComparisonsFrom(final AbstractBoundedInt other) {
        for (final Pair<IntegerRelationType, BigInteger> comparison : other.wasComparedTo) {
            this.wasComparedTo.add(comparison);
        }
    }

    private void computeCosts(AbstractBoundedInt newInt, AbstractBoundedInt resultInt, AbstractNumberMergeResult result) {
        if(! this.containsInt(resultInt)){
            boolean old_got_new_lower_infinity = !resultInt.getLower().isFinite() && this.getLower().isFinite();
            boolean old_got_new_upper_infinity = !resultInt.getUpper().isFinite() && this.getUpper().isFinite();
            if(old_got_new_upper_infinity || old_got_new_lower_infinity){
                result.setVarBtoMerged(CostType.INTERVAL_INFINITE);
            } else {
                result.setVarBtoMerged(CostType.INTERVAL_FINITE);
            }
        } else {
            result.setVarBtoMerged(CostType.NONE);
        }

        if(! newInt.containsInt(resultInt)){
            boolean new_got_new_lower_infinity = !resultInt.getLower().isFinite() && newInt.getLower().isFinite();
            boolean new_got_new_upper_infinity = !resultInt.getUpper().isFinite() && newInt.getUpper().isFinite();
            if(new_got_new_upper_infinity || new_got_new_lower_infinity){
                result.setVarAtoMerged(CostType.INTERVAL_INFINITE);
            } else {
                result.setVarAtoMerged(CostType.INTERVAL_FINITE);
            }
        } else {
            result.setVarAtoMerged(CostType.NONE);
        }

    }

    private AbstractBoundedInt generalizeLowerBound(final IntegerType intType,
                                                    final AbstractBoundedInt newInt,
                                                    final AbstractNumberMergeResult result,
                                                    final int mergeToExtremeValCountThreshold,
                                                    AbstractBoundedInt resultVar) {
        boolean lbMightNeedGeneralization = resultVar.getLowerCounter() > mergeToExtremeValCountThreshold &&
                                            newInt.getLower().compareTo(this.getLower()) < 0;
        AbstractBoundedInt res = resultVar;
        if (lbMightNeedGeneralization) {
            if (resultVar.getLower().compareTo(intType.getLower()) > 0
                && resultVar.getLower().compareTo(resultVar.getMinLower()) > 0
                && newInt.getLower().compareTo(resultVar.getLower()) > 0
                && newInt.getUpper().equals(resultVar.getUpper()))
            {
                res = this.widenLowerBoundHeuristically(intType, result, resultVar);
            } else if (!resultVar.getLower().equals(this.getMinLower()) ||
                       !resultVar.getLower().equals(newInt.getMinLower()))
            {
                res = AbstractBoundedInt.widenLowerBoundToTypeMin(intType, result, resultVar);
            }
        }
        return res;
    }

    private AbstractBoundedInt generalizeUpperBound(final IntegerType intType,
                                                    final AbstractBoundedInt newInt,
                                                    final AbstractNumberMergeResult result,
                                                    final int mergeToExtremeValCountThreshold,
                                                    AbstractBoundedInt resultVar) {
        AbstractBoundedInt res = resultVar;
        boolean ubMightNeedGeneralization = resultVar.getUpperCounter() > mergeToExtremeValCountThreshold &&
                                            newInt.getUpper().compareTo(this.getUpper()) > 0;
        if (ubMightNeedGeneralization) {
            if (!resultVar.getUpper().equals(newInt.getMaxUpper())
                && resultVar.getUpper().compareTo(resultVar.getMaxUpper()) < 0
                && newInt.getLower().equals(resultVar.getLower())
                && newInt.getUpper().compareTo(resultVar.getUpper()) < 0)
            {
                res = this.widenUpperBoundHeuristically(intType, result, resultVar);
            } else if (resultVar.getUpper().compareTo(intType.getUpper()) < 0 &&
                      (!resultVar.getUpper().equals(this.getMaxUpper()) ||
                             !resultVar.getUpper().equals(newInt.getMaxUpper())))
            {
                res = AbstractBoundedInt.widenUpperBoundToTypeMax(intType, result, resultVar);
            }
        }
        return res;
    }

    private AbstractBoundedInt increaseCounter(AbstractBoundedInt newInt, AbstractBoundedInt resultVar) {
        final boolean newLowerBoundChanged = newInt.getLower().compareTo(this.getLower()) < 0 ;
        final boolean newUpperBoundChanged = newInt.getUpper().compareTo(this.getUpper()) > 0;

        AbstractBoundedInt res = resultVar;
        // increase the counter if we had to change something
            int newLowerCounter = resultVar.getLowerCounter();
            if (newLowerBoundChanged) {
                newLowerCounter++;
            }

            int newUpperCounter = resultVar.getUpperCounter();
            if (newUpperBoundChanged) {
                newUpperCounter++;
            }
            res =
                AbstractBoundedInt.create(
                    resultVar.getLower(),
                    resultVar.getUpper(),
                    resultVar.containsLiteral(0),
                    resultVar.getMinLower(),
                    resultVar.getMaxUpper(),
                    newLowerCounter,
                    newUpperCounter);
        return res;
    }

    private AbstractBoundedInt widenLowerBoundHeuristically(final IntegerType intType,
                                                            final AbstractNumberMergeResult result,
                                                            AbstractBoundedInt resultVar) {
        /*
         * this [4, 8] and that [8, 16] are merged to [4, 16]
         * that.lower:  8 >  4
         * that.upper: 16 = 16
         * => go towards the maximal next suspected lower bound, or -inf
         */
        IntervalBound newLowerBound = intType.getLower();

        //Try to guess a better lower bound:
        if (this instanceof IntervalBoundedInt) {
            /* Try to base this on all concrete values against this
             * was compared. Get all of them; check if they are small
             * enough to serve as new lower bound; get the maximum of
             * those matching these criteria.
             */
            final Set<Pair<IntegerRelationType, BigInteger>> thisComparisons =
                    ((IntervalBoundedInt) this).getComparedValues();

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
        result.setEnforcedWideningCost(CostType.INTERVAL_INFINITE);
        return AbstractBoundedInt.create(
                                         newLowerBound,
                                         resultVar.getUpper(),
                                         resultVar.containsLiteral(0) || newLowerBound.isZero(),
                                         resultVar.getMinLower(),
                                         resultVar.getMaxUpper(),
                                         resultVar.getLowerCounter(),
                                         resultVar.getUpperCounter());
    }

    private AbstractBoundedInt widenUpperBoundHeuristically(
            final IntegerType intType, final AbstractNumberMergeResult result,
            AbstractBoundedInt resultVar) {
        IntervalBound newUpperBound = intType.getUpper();

        //Try to guess a better upper bound:
        if (this instanceof IntervalBoundedInt) {
            /* Try to base this on all concrete values against this
             * was compared. Get all of them; check if they are big
             * enough to serve as new upper bound; get the minimum of
             * those matching these criteria.
             */
            final Set<Pair<IntegerRelationType, BigInteger>> thisComparisons =
                ((IntervalBoundedInt) this).getComparedValues();

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
        result.setEnforcedWideningCost(CostType.INTERVAL_INFINITE);
        return AbstractBoundedInt.create(
                                         resultVar.getLower(),
                                         newUpperBound,
                                         resultVar.containsLiteral(0) || newUpperBound.isZero(),
                                         resultVar.getMinLower(),
                                         resultVar.getMaxUpper(),
                                         resultVar.getLowerCounter(),
                                         resultVar.getUpperCounter());
    }

    /**
     * @author Florian Frohn
     * Exception thrown whenever an integer-overflow occurs
     */
    public static class OverflowException extends Exception {

        /**
         * For serialization.
         */
        private static final long serialVersionUID = 7120109695896860408L;

        /**
         * type of operation that caused the overflow
         * if <code>op == null</code>, the overflow was caused by a cast
         */
        private final ArithmeticOperationType op;

        /**
         * type of the variable affected by the overflow
         */
        private final IntegerType type;

        /**
         * truncated value of the variable after the overflow
         */
        private final AbstractBoundedInt value;

        /**
         * @param typeArg {@link OverflowException#type}
         * @param opArg {@link OverflowException#op}
         * @param valueArg {@link OverflowException#value}
         */
        public OverflowException(final IntegerType typeArg, final ArithmeticOperationType opArg, final AbstractBoundedInt valueArg) {
            this.type = typeArg;
            this.op = opArg;
            this.value = valueArg;
        }

        /**
         * @return {@link OverflowException#op}
         */
        public ArithmeticOperationType getOp() {
            return this.op;
        }

        /**
         * @return {@link OverflowException#type}
         */
        public IntegerType getType() {
            return this.type;
        }

        /**
         * @param ignoreOverflows iff true, returns the (mathematically) correct result of the operation. Otherwise,
         *  moves the value back into its bounds.
         * @return {@link OverflowException#value}
         */
        public AbstractBoundedInt getValue(final boolean ignoreOverflows) {
            if (ignoreOverflows) {
                return this.value;
            } else {
                final IntervalBound lowBound = this.value.getLower();
                final IntervalBound upBound = this.value.getUpper();
                assert (lowBound.isFinite() && upBound.isFinite()) : "Am handling overflow, but have infinite bounds. Da fuq?";
                BigInteger low = lowBound.getConstant();
                BigInteger up = upBound.getConstant();

                /*
                 * We can only do something if the difference between the two bounds is smaller than the numbers we can
                 * represent:
                 */
                if (up.subtract(low).abs().compareTo(this.getType().getNumberOfValues()) <= 0) {
                    /*
                     * Then, move the interval back into the bounds: First move the whole interval "down" into the
                     * representable range:
                     */
                    while (up.compareTo(this.type.getUpper().getConstant()) > 0) {
                        up = up.subtract(this.getType().getNumberOfValues());
                        low = low.subtract(this.getType().getNumberOfValues());
                    }
                    /*
                     * After that, check that the lower bound is still in range and do a wraparound for all other cases:
                     */
                    while (low.compareTo(this.type.getLower().getConstant()) < 0) {
                        low = low.add(this.getType().getNumberOfValues());
                    }

                    // If this is still an interval, we've won:
                    if (low.compareTo(up) < 0) {
                        final IntervalBound newLowBound = IntervalBound.create(low);
                        final IntervalBound newUpBound = IntervalBound.create(up);
                        return AbstractBoundedInt.create(
                            newLowBound,
                            newUpBound,
                            this.value.getLower().min(newLowBound),
                            this.value.getUpper().min(newUpBound),
                            this.value.getLowerCounter(),
                            this.value.getUpperCounter());
                    }
                }

                //Sorry, no idea:
                return AbstractBoundedInt.create(this.getType().getLower(), this.getType().getUpper(), this
                    .getType()
                    .getLower(), this.getType().getUpper(), this.value.getLowerCounter(), this.value.getUpperCounter());
            }
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            return
                "overflow: " + (this.op == null ? "cast" : this.op.toString()) + " not representable in " + this.type;
        }
    }

}
