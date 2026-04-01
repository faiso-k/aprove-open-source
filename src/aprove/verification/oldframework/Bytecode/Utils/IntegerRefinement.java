package aprove.verification.oldframework.Bytecode.Utils;

import static aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.IntegerRelationType.*;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Convenience class holding several routines needed in the refinement of
 * abstract integers
 * @author Marc Brockschmidt, Fabian K&uuml;rten
 */
public final class IntegerRefinement {
    /**
     * Private dummy constructor to prevent instantiation.
     */
    private IntegerRefinement() {
        assert (false) : "IntegerRefinement should never be instantiated";
    }

    /**
     * Given two abstract ints <code>x</code>, <code>y</code> and a relation
     * <code>rel</code>, compute, if possible, a collection of pairs of abstract
     * ints {(<code>x1</code>, <code>y1</code>), ..., (<code>xn</code>,
     * <code>yn</code>)} such that for at least one 1 <= i <= n the expression
     * <code>xi rel yi</code> is decidable.
     * @param x the value of the first argument
     * @param y the value of the second argument
     * @param rel the comparison that should be evaluated
     * @return the refined values (or null if that was not possible)
     */
    public static Collection<Pair<AbstractInt, AbstractInt>> forIntegerRelation(final AbstractInt x,
        final AbstractInt y,
        final IntegerRelationType rel) {

        //Easiest case: No refinement possible:
        if (x.isLiteral() && y.isLiteral()) {
            return null;
        }

        // Another simple case: We can already decide this comparision:
        // We don't know anything about sameRef here
        if (AbstractInt.isDecidableComparison(rel, x, y, false, false)) {
            return null;
        }

        // Case 1: x is an literal int:
        if (x.isLiteral()) {
            return IntegerRefinement.forIntegerRelationLiteralInterval(x, y, rel);
        }
        // Case 2: y is an literal int:
        if (y.isLiteral()) {
            final Collection<Pair<AbstractInt, AbstractInt>> mirrored =
                IntegerRefinement.forIntegerRelationLiteralInterval(y, x, rel.mirror());
            final Collection<Pair<AbstractInt, AbstractInt>> result =
                new LinkedHashSet<Pair<AbstractInt, AbstractInt>>(2);
            // swap them all
            for (final Pair<AbstractInt, AbstractInt> p : mirrored) {
                result.add(new Pair<AbstractInt, AbstractInt>(p.y, p.x));
            }
            return result;
        }

        // Now only remain the complex cases: Two overlapping  intervals
        // We decided to ignore these for the following reasons.
        // - the cases we can handle are quite rare
        // - it requires quite complex code
        // - it produces usually more than two pairs, which means that a split might be cheaper
        return null;
    }

    /**
     * Sub method of
     * {@link #forIntegerRelation(AbstractInt, AbstractInt, IntegerRelationType)}
     * for the case that <code>x</code> is an literal and <code>y</code> is an
     * interval. Also, the comparision <code>x rel y</code> should not already
     * be decidable.
     * @param x a literal
     * @param y an interval
     * @param rel the relation
     * @return a set of refinements, note that this method should always find a
     * refinement
     * @see #forIntegerRelation(AbstractInt, AbstractInt, IntegerRelationType)
     */
    private static Collection<Pair<AbstractInt, AbstractInt>> forIntegerRelationLiteralInterval(final AbstractInt x,
        final AbstractInt y,
        final IntegerRelationType rel) {

        if (Globals.useAssertions) {
            assert x.isLiteral() : "x should be a literal";
            assert !y.isLiteral() : "y should NOT be a literal";
            // x should be inside y, or we do not need a refine
            // however, x=0 and y might exclude zero, therefore don't use contains.
            assert y.getLower().compareTo(x.getLiteral()) <= 0;
            assert y.getUpper().compareTo(x.getLiteral()) >= 0;
            assert y.containsLiteral(x.getLiteral()) || x.isZero();
        }

        final Collection<Pair<AbstractInt, AbstractInt>> result = new LinkedHashSet<Pair<AbstractInt, AbstractInt>>(2);

        final BigInteger xLiteral = x.getLiteral();
        final IntervalBound a = y.getLower();
        final IntervalBound b = y.getUpper();

        /*
         * generally we refine y in up to three segments:
         * [a ... x[
         *         [x,x]
         *             ]x ... b]
         * depending on the relation, we can merge some of then
         *
         * For x < y and x >= y we have [a ... x] and ]x ... b]
         * For x > y and x <= y we have [a ... x[ and [x ... b]
         * For x = y and x != y we have [a.... x[ and x and ]x ... b]
         *
         * For the special case 0 = y or 0 != y we just make use the
         * "contains 0" bit.
         *
         * After these segments are created, we throw out 0 if we know it was
         * not contained in the original y interval.
         */

        // special case for 0 = y and 0 != y
        if (x.isZero() && (rel.equals(EQ) || rel.equals(NE))) {
            result.add(new Pair<AbstractInt, AbstractInt>(x, y.removeZeroFromInteger()));
            result.add(new Pair<AbstractInt, AbstractInt>(x, x));
            return result;
        }

        // Segment zero:
        final AbstractInt y0;
        switch (rel) {
        case EQ:
        case NE:
        case LE:
        case GT:
            if (a.compareTo(xLiteral) < 0) {
                // In these cases: x rel y = [a ... x[
                // x  =            x
                // y  = [a     ...    b]
                // results in
                // y0 = [a ... x-1]
                final BigInteger xMinus1 = xLiteral.subtract(BigInteger.ONE);
                final IntervalBound xM1Bound = IntervalBound.create(xMinus1);
                y0 =
                    AbstractInt.create(a, xM1Bound, y.getMinLower(), y.getMaxUpper(), y.getLowerCounter(),
                        y.getUpperCounter());
                result.add(new Pair<>(x, y0));
            }
            break;
        case GE:
        case LT:
            if (a.compareTo(xLiteral) <= 0) {
                // In these cases: [a ... x]
                // x  =        x
                // y  = [a    ...   b]
                // results in
                // y0 = [a ... x]
                final IntervalBound xBound = IntervalBound.create(xLiteral);
                y0 =
                    AbstractInt.create(a, xBound, y.getMinLower(), y.getMaxUpper(), y.getLowerCounter(),
                        y.getUpperCounter());
                result.add(new Pair<>(x, y0));
            }
            break;
        default:
            assert false : "Unknown relation.";
        }

        // Segment one:
        switch (rel) {
        case EQ:
        case NE:
            // We are looking at [x]
            result.add(new Pair<AbstractInt, AbstractInt>(x, x));
            break;
        case LT:
        case GE:
        case GT:
        case LE:
            // no segment
            break;
        default:
            assert false : "Unknown relation.";
        }

        // Segment two
        final AbstractInt y2;
        switch (rel) {
        case EQ:
        case NE:
        case GE:
        case LT:
            if (b.compareTo(xLiteral) > 0) {
                // In these cases: ]x ... b]
                // x  =     x
                // y  = [a     ...    b]
                // results in
                // y2 =      [x+1 ... b]
                final BigInteger xPlus1 = xLiteral.add(BigInteger.ONE);
                final IntervalBound xP1Bound = IntervalBound.create(xPlus1);
                y2 =
                    AbstractInt.create(xP1Bound, b, y.getMinLower(), y.getMaxUpper(), y.getLowerCounter(),
                        y.getUpperCounter());
                result.add(new Pair<AbstractInt, AbstractInt>(x, y2));
            }
            break;
        case LE:
        case GT:
            if (b.compareTo(xLiteral) >= 0) {
                // In these cases: [x ... b]
                // x  =        x
                // y  = [a    ...    b]
                // results in
                // y2 =       [x ... b]
                final IntervalBound xBound = IntervalBound.create(xLiteral);
                y2 =
                    AbstractInt.create(xBound, b, y.getMinLower(), y.getMaxUpper(), y.getLowerCounter(),
                        y.getUpperCounter());
                result.add(new Pair<>(x, y2));
            }
            break;
        default:
            assert false : "Unknown relation.";
        }

        /*
         * It could be that one of the segments still contains zero although the
         * original interval does not contain zero: throw it out.
         */
        if (!y.containsLiteral(0)) {
            final Collection<Pair<AbstractInt, AbstractInt>> cleanedResult =
                new LinkedHashSet<Pair<AbstractInt, AbstractInt>>(2);
            for (final Pair<AbstractInt, AbstractInt> p : result) {
                final AbstractInt ySegment = p.y;
                if (ySegment.containsLiteral(0)) {
                    if (ySegment.isLiteral()) {
                        // 0 without 0 is not good
                        continue;
                    }
                    cleanedResult.add(new Pair<AbstractInt, AbstractInt>(x, ySegment.removeZeroFromInteger()));
                } else {
                    cleanedResult.add(p);
                }
            }
            return cleanedResult;
        }

        return result;
    }
}
