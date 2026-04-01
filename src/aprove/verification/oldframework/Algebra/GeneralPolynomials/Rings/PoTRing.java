/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings;

import java.math.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import immutables.*;

/**
 * A ring that is able to operate on PoT numbers.
 * @author cotto
 */
public class PoTRing extends SubsetOfQRing<PoT> {
    /**
     * Just negate the numerator.
     * @param target a/b.
     * @return -a/b.
     */
    @Override
    public PoT getInverse(final PoT target) {
        ImmutablePair<BigInteger, BigInteger> pair = target.getPair();
        return PoT.create(pair.x.negate(), pair.y);
    }

    /**
     * Return the difference of the two PoTs.
     * @param minuend a/b
     * @param subtrahend c/d
     * @return a/b + (-(c/d)) = a/b + (-c)/d = a/b - c/d
     */
    @Override
    public PoT minus(final PoT minuend, final PoT subtrahend) {
        return this.plus(minuend, this.getInverse(subtrahend));
    }

    /**
     * @return one.
     */
    @Override
    public PoT one() {
        return PoT.ONE;
    }

    /**
     * Add the two given numbers, shift the 2^k part if needed.
     * @param first The first addend.
     * @param second The second addend.
     * @return a/b + c/d
     */
    @Override
    public PoT plus(final PoT first, final PoT second) {
        ImmutablePair<BigInteger, BigInteger> p1 = first.getPair();
        ImmutablePair<BigInteger, BigInteger> p2 = second.getPair();
        BigInteger exp = p1.y.subtract(p2.y);
        if (exp.signum() < 0) {
            exp = BigInteger.ZERO;
        }
        BigInteger a = p1.x.shiftLeft(exp.intValue());
        exp = p2.y.subtract(p1.y);
        if (exp.signum() < 0) {
            exp = BigInteger.ZERO;
        }
        a = a.add(p2.x.shiftLeft(exp.intValue()));
        BigInteger b = p1.y;
        if (p1.y.compareTo(p2.y) > 0) {
            b = p2.y;
        }
        return PoT.create(a, b);
    }

    /**
     * Multiply the two given numbers.
     * @param first The first factor.
     * @param second The second factor.
     * @return the product.
     */
    @Override
    public PoT times(final PoT first, final PoT second) {
        ImmutablePair<BigInteger, BigInteger> p1 = first.getPair();
        ImmutablePair<BigInteger, BigInteger> p2 = second.getPair();
        BigInteger a = p1.x.multiply(p2.x);
        BigInteger b = p1.y.add(p2.y);
        return PoT.create(a, b);
    }

    /**
     * @return zero.
     */
    @Override
    public PoT zero() {
        return PoT.ZERO;
    }

}
