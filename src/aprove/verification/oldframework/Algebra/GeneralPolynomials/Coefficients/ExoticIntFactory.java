package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import java.math.*;

/**
 * A factory for exotic integers.
 * Used to abstract away from the concrete classes.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
abstract public class ExoticIntFactory<T extends ExoticInt<T>> implements GPolyCoeffFactory<T> {

    /**
     * Create a new exotic number of type T with the given value.
     */
    @Override
    abstract public T fromInteger(BigInteger from);
    abstract public T create(BigInteger i);
    abstract public T create(int i);

    /**
     * Return the semiring's one element.
     */
    abstract public T one();

    /**
     * Return the semiring's zero element.
     */
    abstract public T zero();
}
