/**
 *
 */
package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import java.math.*;

/**
 * A small interface for whenever we need to directly create coefficients from integers
 *
 * @author bearperson
 * @version $Id$
 */
public interface GPolyCoeffFactory<C extends GPolyCoeff> {
    /**
     * Creates a coefficient representing the equivalent of the given integer.
     * (only makes sense for coefficients representing ints/rationals)
     */
    C fromInteger(BigInteger from);
}