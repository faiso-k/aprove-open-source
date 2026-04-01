/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import java.math.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.xml.*;
import immutables.*;

/**
 * Represents powers of two like 2^(-3) = 1/8, 2^0 = 1, 2^2 = 4. Additionally
 * 0 can be represented.
 *
 * To store these values a pair is used.
 * 0 is [0  , 0  ]
 * m is [i  , j  ] with m = i*2^j (m != 0, i odd)
 * @author cotto
 */
public final class PoT extends RationalCoeff.RationalCoeffSkeleton implements XMLObligationExportable, CPFAdditional {
    /**
     * This pair stores the value as x*2^y (0 is 0*2^0 by definition).
     */
    private final ImmutablePair<BigInteger, BigInteger> pair;
    /**
     * 1 is 1*2^0 = [1, 0].
     */
    public static final PoT ONE = new PoT(BigInteger.ONE, BigInteger.ZERO);

    /**
     * 0 is 0*2^0 = [0, 0].
     */
    public static final PoT ZERO = new PoT(BigInteger.ZERO, BigInteger.ZERO);

    /**
     * 2 is often used, so create it once.
     */
    private static final BigInteger BIGINTTWO = BigInteger.valueOf(2);

    /**
     * Create a new PoT object defined by the given pair elements.
     * @param first The first element of the pair (coefficient).
     * @param second The second element of the pair (power of two).
     */
    private PoT(final BigInteger first, final BigInteger second) {
        if (Globals.useAssertions) {
            assert (!(first.equals(BigInteger.ZERO)
                    && !second.equals(BigInteger.ZERO)));
        }
        this.pair =
            ImmutableCreator.<BigInteger, BigInteger>create(first, second);
    }

    /**
     * Create a new PoT object defined by the given pair elements.
     * @param first The first element of the pair (coefficient).
     * @param second The second element of the pair (power of two).
     * @return the new PoT.
     */
    public static PoT create(final BigInteger first, final BigInteger second) {
        if (first.equals(BigInteger.ZERO)) {
            return PoT.ZERO;
        } else {
            return new PoT(first, second);
        }
    }

    /**
     * @return true iff the other object is a PoT and the pairs are equal.
     * @param other The object to compare with.
     */
    @Override
    public boolean equals(final Object other) {
        if (other != null && other instanceof PoT) {
            final PoT pot = (PoT) other;
            return this.pair.equals(pot.pair);
        } else {
            return false;
        }
    }

    /**
     * @return a hashcode derived from the pair which defines the PoT.
     */
    @Override
    public int hashCode() {
        return this.pair.hashCode();
    }

    /**
     * @return this pair.
     */
    public ImmutablePair<BigInteger, BigInteger> getPair() {
        return this.pair;
    }

    /**
     * @return the denominator as BigInteger.
     */
    @Override
    public BigInteger getDenominator() {
        if (this.pair.x.equals(BigInteger.ZERO)) {
            // 0*2^y => 0/1
            return BigInteger.ONE;
        } else if (this.pair.y.signum() >= 0) {
            // x*2^y with y>=0 => x*2^y/1
            return BigInteger.ONE;
        } else {
            // x*2^(-y) with (-y)<0 => x/(2^y)
            return PoT.BIGINTTWO.pow(-this.pair.y.intValue());
        }
    }

    /**
     * @return the numerator as BigInteger.
     */
    @Override
    public BigInteger getNumerator() {
        if (this.pair.x.equals(BigInteger.ZERO)) {
            // 0*2^y => 0/1
            return BigInteger.ZERO;
        } else if (this.pair.y.signum() >= 0) {
            // x*2^y with y>=0 => x*2^y/1
            return PoT.BIGINTTWO.pow(this.pair.y.intValue()).multiply(this.pair.x);
        } else {
            // x*2^(-y) with (-y)<0 => x/(2^y)
            return this.pair.x;
        }
    }

    /**
     * @param m Some value.
     * @return a PoT representing the given value.
     */
    public static PoT create(final BigInteger m) {
        final int lowBit = m.getLowestSetBit();
        final BigInteger j = BigInteger.valueOf(lowBit);
        final BigInteger i = m.shiftRight(lowBit);
        return PoT.create(i, j);
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final BigInteger theValue = this.pair.x.multiply(this.pair.y.multiply(BigInteger.valueOf(2)));
        return XMLTag.createInteger(doc, theValue + "");
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final BigInteger theValue = this.pair.x.multiply(this.pair.y.multiply(BigInteger.valueOf(2)));
        final Element integer = CPFTag.INTEGER.createElement(doc);
        integer.appendChild(doc.createTextNode("" + theValue));
        return integer;
    }

}
