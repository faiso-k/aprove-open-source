package aprove.verification.oldframework.Utility;

import aprove.*;

/**
 * Abstract class to provide some additional mathematical functions
 * which are not provided by java.lang.Math.
 *
 * @author fuhs
 * @version $Id$
 */
public abstract class AProVEMath {

    /**
     * Returns <code>base<sup>exponent</sup></code>.
     * Works considerably faster than java.lang.Math.pow(double, double).
     *
     * @param base base of the power
     * @param exponent non-negative exponent of the power
     * @return base<sup>exponent</sup>
     */
    public static int power (int base, int exponent) {
        if (Globals.useAssertions) {
            assert (exponent >= 0);
        }
        if (exponent == 0) {
            return 1;
        }
        else if (exponent == 1) {
            return base;
        }
        else if (base == 2) {
            return base << (exponent-1);
        }
        else {
            int result = 1;
            while (exponent > 0) {
                if (exponent % 2 == 1) {
                    result *= base;
                }
                base *= base;
                exponent /= 2;
            }
            return result;
        }
    }

    /**
     * Return how many bits it takes to represent <code>n</code>.
     *
     * @param n - must be non-negative
     * @return the number of bits it takes to represent n in binary
     */
    public static int binaryLength (int n) {
        if (Globals.useAssertions) {
            assert n >= 0;
        }
        return 32 - Integer.numberOfLeadingZeros(n);
    }

    /**
     * @param n
     * @return the smallest non-negative integer z such that
     *  z*z >= n (i.e., for n >= 0, we have z = ceil(sqrt(n)))
     */
    public static int ceilSqrt(int n) {
        int z = 0;
        while (z*z < n) {
            ++z;
        }
        return z;
    }

    /**
     * @param x
     * @param y - non-zero
     * @return the smallest int z such that z*y >= x
     *  (e.g., ceilDiv(10, 3) should yield 4)
     */
    public static int ceilDiv(int x, int y) {
        int z = x / y;
        int product = y * z;
        return product == x || z < 0 ? z : z + 1;
    }
}
