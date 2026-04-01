package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import java.math.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;

/**
 * Abstract ancestor of arctic and tropical integers.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
abstract public class ExoticInt<T extends ExoticInt<T>> implements GPolyCoeff {

    protected BigInteger value;
    protected boolean finite;

    protected ExoticInt(BigInteger value) {
        this.value = value;
        this.finite = true;
    }

    /**
     * @return the BigInteger value of this
     */
    public BigInteger getValue() {
        return this.value;
    }

    /**
     * Returns true iff this is an actual number, and not
     * plus / minus infinity.
     */
    public boolean isFinite() {
        return this.finite;
    }

    /**
     * Returns true iff this has a value of 0 or greater.
     */
    abstract public boolean isPositive();

    /**
     * Addition (min/max).
     */
    abstract public T plus(T other);

    /**
     * Multiplication (plus).
     * Stupid Java generics won't allow me to put the actual
     * implementation here, even though it's the same for
     * both arctic and tropical ints :(
     */
    abstract public T times(T other);

    /**
     * Returns the value of this ArcticInt as an integer.
     * Only yields correct results when called on a finite ArcticInt.
     */
    public int intValue() {
        if (Globals.useAssertions) {
            assert(this.finite);
        }
        return this.getValue().intValue();
    }

    abstract public T abs();

    abstract public int signum();

    abstract public boolean isGreater(T other);

    abstract public boolean isGreaterOrEqual(T other);

    @Override
    abstract public String export(Export_Util o);

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }
}