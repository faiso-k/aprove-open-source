/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import java.math.*;

import aprove.prooftree.Export.Utility.*;

/**
 * All classes implementing this interface somehow represent coefficients as
 * rational numbers. The most general form of a rational number is p/q, so
 * these classes can and must be able to return the numerator and denominator.
 */
public interface RationalCoeff extends GPolyCoeff {
    /**
     * German: Zaehler.
     * @return the numerator as BigInteger.
     */
    BigInteger getNumerator();

    /**
     * German: Nenner.
     * @return the denominator as BigInteger.
     */
    BigInteger getDenominator();

    /**
     * Provide basic functionality.
     * @author cotto
     */
    public abstract class RationalCoeffSkeleton implements RationalCoeff {
        /**
         * @return the string representation of this.
         */
        @Override
        public String toString() {
            return this.export(new PLAIN_Util());
        }

        /**
         * Export this fraction.
         * @param o some export util.
         * @return the string representation as defined by the export util.
         */
        @Override
        public String export(final Export_Util o) {
            BigInteger num = this.getNumerator();
            BigInteger denom = this.getDenominator();
            String numString = num.toString();
            String denomString = denom.toString();
            if (num.equals(BigInteger.ZERO)) {
               return numString;
            } else if (denom.equals(BigInteger.ONE)) {
                return numString;
            } else {
                BigInteger gcd = num.gcd(denom);
                num = num.divide(gcd);
                denom = denom.divide(gcd);
                numString = num.toString();
                denomString = denom.toString();
                return o.fraction(numString, denomString);
            }
        }
    }
}
