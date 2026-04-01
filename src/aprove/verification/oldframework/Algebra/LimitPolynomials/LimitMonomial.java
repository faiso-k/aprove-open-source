package aprove.verification.oldframework.Algebra.LimitPolynomials;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;


/**
 * Specifies a single monomial in a LimitPolynomial.
 * A monomial is characterized by its exponent polynomial, its base polynomial,
 * and its maximum exponent value.
 * @author kabasci
 *
 */
public class LimitMonomial {


    private final SimplePolynomial exponent;
    private final SimplePolynomial base;

    private final int maxExponent;


    /**
     * Compares two LimitMonomial for Sorting.
     * @author kabasci
     *
     */
    public static class MonomialComparator implements Comparator<LimitMonomial> {

        @Override
        public int compare(LimitMonomial arg0, LimitMonomial arg1) {
            // This will work best in specialized instances.
            int res1 = -arg0.exponent.compareTo(arg1.exponent);
            if (res1 == 0) {
                return -arg0.base.compareTo(arg1.base);
            } else {
                return res1;
            }

        }

    }

    /**
     * Creates a new LimitMonomial from the given components.
     * @param exponent
     * @param base
     * @param maxExponent
     */

    public LimitMonomial(SimplePolynomial exponent, SimplePolynomial base, int maxExponent) {
        this.base = base;
        this.exponent = exponent;
        this.maxExponent = maxExponent;
    }


    public SimplePolynomial getExponent() {
        return this.exponent;
    }


    public SimplePolynomial getBase() {
        return this.base;
    }


    public int getMaxExponent() {
        return this.maxExponent;
    }

    @Override
    public String toString() {
        return this.base.toString() +"X^" + this.exponent.toString()+ "[max:" + this.maxExponent + "]";
    }

}
