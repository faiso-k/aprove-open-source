package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import java.math.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.xml.*;

/**
 * A tropical integer is either an integer number or infinity.
 * Pay attention that the tropical numbers use 'min' for addition and
 * 'plus' for multiplication instead of the standard operations
 * known from integers.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class TropicalInt extends ExoticInt<TropicalInt> implements XMLObligationExportable {

    /**
     * The tropical number zero, i.e. infinity.
     */
    public final static TropicalInt ZERO;

    /**
     * The tropical number one, i.e. the natural number 0.
     */
    public final static TropicalInt ONE;

    static {
        ZERO = new TropicalInt(BigInteger.ZERO);
        TropicalInt.ZERO.finite = false;
        ONE = new TropicalInt(BigInteger.ZERO);
    }

    private TropicalInt(final BigInteger value) {
        super(value);
    }

    /**
     * Create a new finite TropicalInt with the given value.
     * For infinity use the constant TropicalInt::ZERO.
     */
    public static TropicalInt create(final BigInteger value) {
        return new TropicalInt(value);
    }

    /**
     * Create a new finite TropicalInt with the given value.
     * For infinity use the constant TropicalInt::ZERO.
     */
    public static TropicalInt create(final int value) {
        return new TropicalInt(BigInteger.valueOf(value));
    }

    /**
     * The tropical addition operation, returns an TropicalInt whose value
     * is the minimum of the values of this and other.
     * @param other Some TropicalInt to add to this one.
     */
    @Override
    public TropicalInt plus(final TropicalInt other) {
        if (! other.finite) {
            return this;
        }
        if (! this.finite) {
            return other;
        }
        return this.value.compareTo(other.value) <= 0 ? this : other;
    }

    /**
     * The tropical multiplication operation, returns an TropicalInt
     * whose value is the sum of the values of this and other.
     * Obviously, infinity plus any value is still infinity.
     * @param other Some TropicalInt to multiply with this.
     */
    @Override
    public TropicalInt times(final TropicalInt other) {
        if (!this.finite || !other.finite) {
            return TropicalInt.ZERO;
        }
        return new TropicalInt(this.value.add(other.value));
    }

    @Override
    public boolean isPositive() {
        return !this.finite || this.value.signum() >= 0;
    }

    /**
     * Returns the signum of the value of this TropicalInt, or 1 if it
     * is infinity.
     */
    @Override
    public int signum() {
        if (!this.finite) {
            return 1;
        }
        return this.value.signum();
    }

    /**
     * Returns an TropicalInt whose value is the absolute value of this,
     * if this is finite. Otherwise, returns infinity.
     */
    @Override
    public TropicalInt abs() {
        if (!this.finite) {
            return TropicalInt.ZERO;
        }
        return new TropicalInt(this.value.abs());
    }

    /**
     * x > y iff x = ZERO or (x,y \in Z and x > y)
     * (quite, but not entirely, analogous to ArcticInt)
     */
    @Override
    public boolean isGreater(final TropicalInt other) {
        if (! this.finite) {
            return true;
        }
        if (! other.finite) {
            return false;
        }
        return this.value.compareTo(other.value) > 0;
    }

    /**
     * x >= y iff x = ZERO or (x,y \in Z and x >= y)
     */
    @Override
    public boolean isGreaterOrEqual(final TropicalInt other) {
        if (! this.finite) {
            return true;
        }
        if (! other.finite) {
            return false;
        }
        return this.value.compareTo(other.value) >= 0;
    }

    @Override
    public String export(final Export_Util o) {
        if (!this.finite) {
            return "I"; // temporary solution
        } else {
            return this.value.toString() + "T";
        }
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        throw new UnsupportedOperationException();
    }

}