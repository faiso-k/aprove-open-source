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
 * Represent positive fractions n/m by just storing n and m.
 * @author cotto
 */
public final class MbyN extends RationalCoeff.RationalCoeffSkeleton implements XMLObligationExportable, CPFAdditional {
    /**
     * This pair stores the value.
     */
    private final ImmutablePair<BigInteger, BigInteger> pair;

    /**
     * 1 is 1/1.
     */
    public static final MbyN ONE = new MbyN(BigInteger.ONE, BigInteger.ONE);

    /**
     * 0 is 0/1.
     */
    public static final MbyN ZERO = new MbyN(BigInteger.ZERO, BigInteger.ONE);

    /**
     * Create a new MbyN object defined by the given pair elements. The fraction
     * must be truncated.
     * @param first The first element of the pair (numerator).
     * @param second The second element of the pair (denominator).
     */
    private MbyN(final BigInteger first, final BigInteger second) {
        if (Globals.useAssertions) {
            assert (!(first.equals(BigInteger.ZERO)
                    && !second.equals(BigInteger.ONE)));
            assert (second.signum() > 0);
            assert (!first.mod(second).equals(BigInteger.ZERO)
                    || second.equals(BigInteger.ONE));
        }
        this.pair =
            ImmutableCreator.<BigInteger, BigInteger>create(first, second);
    }

    /**
     * Create a new MbyN object defined by the given pair elements.
     * @param first The first element of the pair (numerator).
     * @param second The second element of the pair (denominator).
     * @return the new PoT.
     */
    public static MbyN create(final BigInteger first, final BigInteger second) {
        if (first.equals(BigInteger.ZERO)) {
            return MbyN.ZERO;
        } else {
            return new MbyN(first, second);
        }
    }

    /**
     * @return true iff the other object is a MbyN and the values defined by
     * both are equal.
     * @param other The object to compare with.
     */
    @Override
    public boolean equals(final Object other) {
        if (other != null && other instanceof MbyN) {
            final MbyN mByN = (MbyN) other;
            return (this.pair.equals(mByN.pair));
        } else {
            return false;
        }
    }

    /**
     * @return a hashcode derived from the pair which defines the MbyN.
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
        return this.pair.y;
    }

    /**
     * @return the numerator as BigInteger.
     */
    @Override
    public BigInteger getNumerator() {
        return this.pair.x;
    }

    /**
     * @param m Some value.
     * @return a MbyN representing the given value.
     */
    public static MbyN create(final BigInteger m) {
        return MbyN.create(m, BigInteger.ONE);
    }

    /**
     * @param m
     *            Some String that represents the MbyN value.
     * @return a MbyN representing the given value.
     */
    public static MbyN create(String s) {
        BigInteger numerator;
        BigInteger denominator;
        s = s.replaceAll(" ", "");
        final String[] ar = s.split("/");
        assert (ar.length == 1 || ar.length == 2);
        numerator = new BigInteger(ar[0]);
        if (ar.length > 1) {
            denominator = new BigInteger(ar[1]);
        } else {
            denominator = BigInteger.ONE;
        }

        return MbyN.create(numerator, denominator);
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element rational = XMLTag.RATIONAL.createElement(doc);

        final Element numerator = XMLTag.NUMERATOR.createElement(doc);
        numerator.setAttribute("value", this.getNumerator().toString());

        final Element denominator = XMLTag.DENOMINATOR.createElement(doc);
        denominator.setAttribute("value", this.getDenominator().toString());

        rational.appendChild(numerator);
        rational.appendChild(denominator);

        return rational;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element rational = CPFTag.RATIONAL.createElement(doc);

        final Element numerator = CPFTag.NUMERATOR.createElement(doc);
        numerator.appendChild(doc.createTextNode( this.getNumerator().toString()));

        final Element denominator = CPFTag.DENOMINATOR.createElement(doc);
        denominator.appendChild(doc.createTextNode(this.getDenominator().toString()));

        rational.appendChild(numerator);
        rational.appendChild(denominator);

        return rational;
    }

}
