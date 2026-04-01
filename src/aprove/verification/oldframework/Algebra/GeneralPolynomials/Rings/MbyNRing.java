/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings;

import java.math.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import immutables.*;

/**
 * A ring that is able to operate on MbyN numbers.
 * @author cotto
 */
public class MbyNRing extends SubsetOfQRing<MbyN> {
    /**
     * Just negate the numerator.
     * @param target a/b.
     * @return -a/b.
     */
    @Override
    public MbyN getInverse(final MbyN target) {
        ImmutablePair<BigInteger, BigInteger> pair = target.getPair();
        return MbyN.create(pair.x.negate(), pair.y);
    }

    /**
     * Return the difference of the two MbyNs.
     * @param minuend a/b
     * @param subtrahend c/d
     * @return a/b + (-(c/d)) = a/b + (-c)/d = a/b - c/d
     */
    @Override
    public MbyN minus(final MbyN minuend, final MbyN subtrahend) {
        return this.plus(minuend, this.getInverse(subtrahend));
    }

    /**
     * @return one.
     */
    @Override
    public MbyN one() {
        return MbyN.ONE;
    }

    /**
     * Add the two given numbers.
     * @param first The first addend.
     * @param second The second addend.
     * @return a/b + c/d
     */
    @Override
    public MbyN plus(final MbyN first, final MbyN second) {
        ImmutablePair<BigInteger, BigInteger> p1 = first.getPair();
        ImmutablePair<BigInteger, BigInteger> p2 = second.getPair();
        if (first.equals(MbyN.ZERO)) {
            return second;
        } else if (second.equals(MbyN.ZERO)) {
            return first;
        }
        BigInteger lcm = p1.y.multiply(p2.y).abs().divide(p1.y.gcd(p2.y));
        BigInteger a = p1.x.multiply(lcm).divide(p1.y);
        BigInteger b = p2.x.multiply(lcm).divide(p2.y);
        BigInteger numerator = a.add(b);
        BigInteger gcd = numerator.gcd(lcm);
        numerator = numerator.divide(gcd);
        lcm = lcm.divide(gcd);
        return MbyN.create(numerator, lcm);
    }

    /**
     * Multiply the two given numbers.
     * @param first The first factor.
     * @param second The second factor.
     * @return the product.
     */
    @Override
    public MbyN times(final MbyN first, final MbyN second) {
        ImmutablePair<BigInteger, BigInteger> p1 = first.getPair();
        ImmutablePair<BigInteger, BigInteger> p2 = second.getPair();
        BigInteger a = p1.x.multiply(p2.x);
        BigInteger b = p1.y.multiply(p2.y);
        BigInteger gcd = a.gcd(b);
        a = a.divide(gcd);
        b = b.divide(gcd);
        return MbyN.create(a, b);
    }

    /**
     * @return zero.
     */
    @Override
    public MbyN zero() {
        return MbyN.ZERO;
    }

}
