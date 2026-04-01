package aprove.verification.oldframework.IntegerReasoning;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Utility functions for integers.
 * @author Marc Brockschmidt, cryingshadow
 */
public abstract class IntegerUtils {

    /**
     * The constant -1.
     */
    public static final BigInteger NEGONE = BigInteger.ONE.negate();

    /**
     * The constant -2.
     */
    public static final BigInteger NEGTWO = BigInteger.valueOf(-2);

    /**
     * The constant 2.
     */
    public static final BigInteger TWO = BigInteger.valueOf(2);

    /**
     * @param bits The number of bits.
     * @return The minimum number of bytes which can hold the specified number of bits.
     */
    public static long bitsToBytes(long bits) {
        return bits % 8 == 0 ? bits / 8 : bits / 8 + 1;
    }

    /**
     * @param exp Some integer term.
     * @return If the specified term does not contain any variables, the constant to which this term evaluates to is
     *         returned. Null otherwise.
     * @throws DivisionByZeroException If the specified term contains a division by zero.
     */
    public static IntegerConstant evaluate(FunctionalIntegerExpression exp) throws DivisionByZeroException {
        if (exp instanceof IntegerVariable) {
            return null;
        }
        if (exp instanceof IntegerConstant) {
            return (IntegerConstant)exp;
        }
        final CompoundFunctionalIntegerExpression term = (CompoundFunctionalIntegerExpression)exp;
        final List<BigInteger> args = new ArrayList<BigInteger>();
        for (FunctionalIntegerExpression arg : term.getArguments()) {
            IntegerConstant c = IntegerUtils.evaluate(arg);
            if (c == null) {
                return null;
            }
            args.add(c.getIntegerValue());
        }
        return
            new PlainIntegerConstant(term.getOperation().evaluateOnIntegers(args.toArray(new BigInteger[args.size()])));
    }

    /**
     * @param firstLower The lower bound of the first interval.
     * @param firstUpper The upper bound of the first interval.
     * @param secondLower The lower bound of the second interval.
     * @param secondUpper The upper bound of the second interval.
     * @return The intersection of the two specified intervals. Null if the intersection is empty.
     */
    public static <C extends IntegerConstant> Pair<C, C> intersection(
        C firstLower,
        C firstUpper,
        C secondLower,
        C secondUpper
    ) {
        C lower = IntegerUtils.max(firstLower, secondLower, false);
        C upper = IntegerUtils.min(firstUpper, secondUpper, true);
        if (lower == null || upper == null || lower.getIntegerValue().compareTo(upper.getIntegerValue()) <= 0) {
            return new Pair<C, C>(lower, upper);
        }
        return null;
    }

    /**
     * @param interval Some interval.
     * @param other Another interval.
     * @return The intersection of the two specified intervals.
     */
    public static <C extends IntegerConstant> Pair<C, C> intersection(Pair<C, C> interval, Pair<C, C> other) {
        return IntegerUtils.intersection(interval.x, interval.y, other.x, other.y);
    }

    /**
     * @param number Some number.
     * @return True if this number is a power of 2. False otherwise.
     */
    public static boolean isPowerOfTwo(int number) {
        if (number <= 0) {
            return false;
        }
        if ((number & -number) == number) {
            return true;
        }
        return false;
    }

    /**
     * @param bits The number of bits for the bounded integer.
     * @param signed Is the integer signed?
     * @return The biggest value representable by the bounded integer.
     */
    public static BigInteger lowerLimitForBoundedInt(int bits, boolean signed) {
        if (signed) {
            return BigInteger.valueOf(2).pow(bits - 1).negate();
        } else {
            return BigInteger.ZERO;
        }
    }

    /**
     * @param a Some constant.
     * @param b Another constant.
     * @return The maximum of the specified constants. A non-null constant is considered bigger than null.
     */
    public static <C extends IntegerConstant> C max(C a, C b) {
        return IntegerUtils.minMax(a, b, false, false);
    }

    /**
     * @param a Some constant.
     * @param b Another constant.
     * @param nullBigger Is null bigger than non-null constants?
     * @return The maximum of the specified constants. A non-null constant is considered less than null iff nullBigger
     *         is true.
     */
    public static <C extends IntegerConstant> C max(C a, C b, boolean nullBigger) {
        return IntegerUtils.minMax(a, b, false, nullBigger);
    }

    /**
     * @param a Some constant.
     * @param b Another constant.
     * @return The minimum of the specified constants. A non-null constant is considered less than null.
     */
    public static <C extends IntegerConstant> C min(C a, C b) {
        return IntegerUtils.minMax(a, b, true, true);
    }

    /**
     * @param a Some constant.
     * @param b Another constant.
     * @param nullBigger Is null bigger than non-null constants?
     * @return The minimum of the specified constants. A non-null constant is considered less than null iff nullBigger
     *         is true.
     */
    public static <C extends IntegerConstant> C min(C a, C b, boolean nullBigger) {
        return IntegerUtils.minMax(a, b, true, nullBigger);
    }

    /**
     * @param relation Some relation.
     * @return True if the relation is a trivial tautology. False if the relation is trivially false. Null otherwise.
     *         Here, trivial means that both sides must be equal or the relation does not contain variables.
     * @throws DivisionByZeroException If the relation contains a division by zero.
     */
    public static Boolean solveTrivially(IntegerRelation relation) throws DivisionByZeroException {
        final FunctionalIntegerExpression lhs = relation.getLhs();
        final FunctionalIntegerExpression rhs = relation.getRhs();
        if (lhs.equals(rhs)) {
            switch (relation.getRelationType()) {
                case NE:
                case LT:
                case GT:
                    return false;
                default:
                    return true;
            }
        }
        final IntegerConstant left = IntegerUtils.evaluate(lhs);
        if (left == null) {
            return null;
        }
        final IntegerConstant right = IntegerUtils.evaluate(rhs);
        if (right == null) {
            return null;
        }
        final int c = left.getIntegerValue().compareTo(right.getIntegerValue());
        switch (relation.getRelationType()) {
            case EQ:
                return c == 0;
            case NE:
                return c != 0;
            case LE:
                return c <= 0;
            case LT:
                return c <= 0;
            case GE:
                return c <= 0;
            case GT:
                return c <= 0;
            default:
                throw new IllegalStateException("Someone found a new way to relate integers...");
        }
    }

    /**
     * @param firstLower The lower bound of the first interval.
     * @param firstUpper The upper bound of the first interval.
     * @param secondLower The lower bound of the second interval.
     * @param secondUpper The upper bound of the second interval.
     * @return The union of the two specified intervals.
     */
    public static <C extends IntegerConstant> Pair<C, C> union(
        C firstLower,
        C firstUpper,
        C secondLower,
        C secondUpper
    ) {
        return
            new Pair<C, C>(
                IntegerUtils.min(firstLower, secondLower, false),
                IntegerUtils.max(firstUpper, secondUpper, true)
            );
    }

    /**
     * @param interval Some interval.
     * @param other Another interval.
     * @return The union of the two specified intervals.
     */
    public static <C extends IntegerConstant> Pair<C, C> union(Pair<C, C> interval, Pair<C, C> other) {
        return IntegerUtils.union(interval.x, interval.y, other.x, other.y);
    }

    /**
     * @param bits The number of bits for the bounded integer.
     * @param signed Is the integer signed?
     * @return The biggest value representable by the bounded integer.
     */
    public static BigInteger upperLimitForBoundedInt(int bits, boolean signed) {
        if (signed) {
            return BigInteger.valueOf(2).pow(bits - 1).subtract(BigInteger.ONE);
        } else {
            return BigInteger.valueOf(2).pow(bits).subtract(BigInteger.ONE);
        }
    }

    /**
     * @param a Some constant.
     * @param b Another constant.
     * @param min Should the minimum (true) or the maximum (false) be returned?
     * @param nullBigger Is null bigger than non-null constants?
     * @return The minimum or maximum of the specified constants. Non-null constants are considered less than null iff
     *         nullBigger is true.
     */
    private static <C extends IntegerConstant> C minMax(C a, C b, boolean min, boolean nullBigger) {
        if (a == null) {
            return min == nullBigger ? b : null;
        }
        if (b == null) {
            return min == nullBigger ? a : null;
        }
        if (a.getIntegerValue().compareTo(b.getIntegerValue()) > 0) {
            return min ? b : a;
        }
        return min ? a : b;
    }

    /**
     * Do not instantiate this.
     */
    private IntegerUtils() {
        throw new UnsupportedOperationException("Do not instantiate me!");
    }

}
