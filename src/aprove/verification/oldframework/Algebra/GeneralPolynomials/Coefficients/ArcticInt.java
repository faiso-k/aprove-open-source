package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import java.math.*;
import java.util.regex.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.xml.*;

/**
 * An arctic integer is either an integer number or negative infinity.
 * Pay attention that the arctic numbers use 'max' for addition and
 * 'plus' for multiplication instead of the standard operations
 * known from integers.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ArcticInt extends ExoticInt<ArcticInt> implements XMLObligationExportable, CPFAdditional {

    /**
     * The arctic number zero, i.e. negative infinity.
     */
    public final static ArcticInt ZERO;

    /**
     * The arctic number one, i.e. the natural number 0.
     */
    public final static ArcticInt ONE;

    static {
        ZERO = new ArcticInt(BigInteger.ZERO);
        ArcticInt.ZERO.finite = false;
        ONE = new ArcticInt(BigInteger.ZERO);
    }

    private ArcticInt(final BigInteger value) {
        super(value);
    }

    /**
     * Create a new finite ArcticInt with the given value.
     * For negative infinity use the constant ArcticInt::ZERO.
     */
    public static ArcticInt create(final BigInteger value) {
        return new ArcticInt(value);
    }

    /**
     * Create a new finite ArcticInt with the given value.
     * For negative infinity use the constant ArcticInt::ZERO.
     */
    public static ArcticInt create(final int value) {
        return new ArcticInt(BigInteger.valueOf(value));
    }

    /**
     * The arctic addition operation, returns an ArcticInt whose value is the maximum
     * of the values of this and other.
     * @param other Some ArcticInt to add to this one.
     */
    @Override
    public ArcticInt plus(final ArcticInt other) {
        if (! other.finite) {
            return this;
        }
        if (! this.finite) {
            return other;
        }
        return this.value.compareTo(other.value) >= 0 ? this : other;
    }

    /**
     * The arctic multiplication operation, returns an ArcticInt whose value is
     * the sum of the values of this and other. Obviously, negative infinity
     * plus any value is still negative infinity.
     * @param other Some ArcticInt to multiply with this.
     */
    @Override
    public ArcticInt times(final ArcticInt other) {
        if (!this.finite || !other.finite) {
            return ArcticInt.ZERO;
        }
        return new ArcticInt(this.value.add(other.value));
    }

    @Override
    public boolean isPositive() {
        return this.finite && this.value.signum() >= 0;
    }

    /**
     * Returns the signum of the value of this ArcticInt, or -1 if it
     * is negative infinity.
     */
    @Override
    public int signum() {
        if (!this.finite) {
            return -1;
        }
        return this.value.signum();
    }

    /**
     * Returns an ArcticInt whose value is the absolute value of this,
     * if this is finite. Otherwise, returns negative infinity.
     */
    @Override
    public ArcticInt abs() {
        if (!this.finite) {
            return ArcticInt.ZERO;
        }
        return new ArcticInt(this.value.abs());
    }

    /**
     * x > y iff y = ZERO or (x,y \in Z and x > y)
     * (cf.: Koprowski/Waldmann, RTA'08)
     */
    @Override
    public boolean isGreater(final ArcticInt other) {
        if (! other.finite) {
            return true;
        }
        if (! this.finite) {
            return false;
        }
        return this.value.compareTo(other.value) > 0;
    }

    /**
     * x >= y iff y = ZERO or (x,y \in Z and x >= y)
     */
    @Override
    public boolean isGreaterOrEqual(final ArcticInt other) {
        if (! other.finite) {
            return true;
        }
        if (! this.finite) {
            return false;
        }
        return this.value.compareTo(other.value) >= 0;
    }

    @Override
    public String export(final Export_Util o) {
        if (!this.finite) {
            return "-I"; // temporary solution
        } else {
            return this.value.toString() + "A";
        }
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        return XMLTag.createArcticInt(doc, !this.finite, this.value);
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        if (this.finite) {
            return CPFTag.INTEGER.create(doc, doc.createTextNode("" + this.value));
        } else {
            return CPFTag.MINUS_INFINITY.create(doc);
        }
    }

    public String toYices() {
        final StringBuilder sb = new StringBuilder("(mk-tuple ");
        sb.append(this.finite ? "false " : "true ");
        sb.append(this.value.intValue());
        sb.append(")");
        return sb.toString();
    }

    private static Matcher matcher = null;

    public static ArcticInt fromYices(final String rep) {
        if (Globals.DEBUG_ULRICHSG || Globals.DEBUG_THETUX) {
            System.out.println("from yices: " + rep);
        }
        if (ArcticInt.matcher == null) {
            ArcticInt.matcher = Pattern.compile("^\\(mk-tuple\\s+(true|false)\\s+([0-9]+)\\)$").matcher(rep);
        } else {
            ArcticInt.matcher.reset(rep);
        }
        if (!ArcticInt.matcher.matches()) {
            throw new IllegalArgumentException("Unrecognized format: " + rep);
        }
        if (ArcticInt.matcher.group(1).equalsIgnoreCase("true")) {
            return ArcticInt.ZERO;
        }
        return ArcticInt.create(Integer.parseInt(ArcticInt.matcher.group(2)));
    }
}