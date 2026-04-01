package aprove.verification.oldframework.LinearArithmetic.Structure;

import java.math.*;

import aprove.prooftree.Export.Utility.*;

/**
 * Represents a rational number. Since this class uses BigIntegers to store
 * numerator & denominator, _every_ rational number can be represented.
 * @author Matthias Hoelzel
 */
public class PreciseRational implements Exportable {
    /**
     * German: Zaehler
     */
    private final BigInteger numerator;

    /**
     * German: Nenner
     */
    private final BigInteger denominator;

    /**
     * Constructor! Creates your new precise rational!
     * @param num some BigInteger for the numerator
     * @param denom some BigInteger for the denominator
     */
    public PreciseRational(final BigInteger num, final BigInteger denom) {
        if (num == null || denom == null) {
            throw new NullPointerException("PreciseRational:Argument is null! (num = "
                + num
                + ", "
                + "denom = "
                + denom
                + ")");
        }
        assert !denom.equals(BigInteger.ZERO) : "Denominator is zero!";

        final BigInteger gcd = num.gcd(denom);

        if (denom.compareTo(BigInteger.ZERO) >= 0) {
            this.numerator = num.divide(gcd);
        } else {
            this.numerator = num.negate().divide(gcd);
        }
        this.denominator = denom.abs().divide(gcd);
    }

    /**
     * Create a rational representing the given integer.
     * @param i some BigInteger
     */
    public PreciseRational(final BigInteger i) {
        this(i, BigInteger.ONE);
    }

    /**
     * Parses a rational number and constructs a precise rational.
     * @param toParse string to be parsed
     * @throws NumberFormatException if the string is not encoding a rational
     * number
     * @return PreciseRational
     */
    public static PreciseRational parseRational(final String toParse) throws NumberFormatException {
        if (toParse.indexOf('/') == (-1)) {
            final BigInteger i = new BigInteger(toParse);
            return new PreciseRational(i);
        } else {
            final int index = toParse.indexOf('/');
            final BigInteger num = new BigInteger(toParse.substring(0, index));
            final BigInteger denom = new BigInteger(toParse.substring(index + 1, toParse.length()));
            return new PreciseRational(num, denom);
        }
    }

    /**
     * Getter for the numerator.
     * @return BigInteger
     */
    public BigInteger getNumerator() {
        return this.numerator;
    }

    /**
     * Getter for the denominator.
     * @return BigInteger
     */
    public BigInteger getDenominator() {
        return this.denominator;
    }

    /**
     * Adds this rational and the given rational and returns the result.
     * @param other the other rational number
     * @return PreciseRational
     */
    public PreciseRational add(final PreciseRational other) {
        if (other == null) {
            return null;
        }

        return new PreciseRational(this.numerator.multiply(other.denominator).add(
            other.numerator.multiply(this.denominator)), this.denominator.multiply(other.denominator));
    }

    /**
     * Multiplies this rational with the given argument and returns the result.
     * @param other the other rational number
     * @return PreciseRational
     */
    public PreciseRational multiply(final PreciseRational other) {
        if (other == null) {
            return null;
        }

        return new PreciseRational(
            this.numerator.multiply(other.numerator),
            this.denominator.multiply(other.denominator));
    }

    /**
     * Compares this rational with the given argument and returns (-1), if this
     * is smaller, or 0, if this equals other, or (+1) number, if this is
     * bigger.
     * @param other some rational number
     * @return int (see description above!)
     */
    public int compareTo(final PreciseRational other) {
        if (other == null) {
            throw new NullPointerException("PreciseRational.compareTo(): Argument is null!");
        }

        return this.numerator.multiply(other.denominator).subtract(other.numerator.multiply(this.denominator)).signum();
    }

    @Override
    public boolean equals(final Object o) {
        if (o == null || !(o instanceof PreciseRational)) {
            return false;
        } else {
            return this.compareTo((PreciseRational) o) == 0;
        }
    }

    /**
     * Raises this to the power.
     * @param exp some integer
     * @return some precise rational
     */
    public PreciseRational power(final int exp) {
        if (exp < 0) {
            return this.invert().power(-exp);
        } else if (exp == 0) {
            return new PreciseRational(BigInteger.ONE);
        } else {
            if (exp % 2 == 0) {
                final PreciseRational rp = this.power(exp / 2);
                return rp.multiply(rp);
            } else {
                final PreciseRational rp = this.power(exp - 1);
                return rp.multiply(this);
            }
        }
    }

    /**
     * Returns the multiplicative inverse of this.
     * @return some rational number
     */
    public PreciseRational invert() {
        if (this.numerator.equals(BigInteger.ZERO)) {
            assert false : "Cannot divide by zero!";
            return null;
        } else {
            return new PreciseRational(this.denominator, this.numerator);
        }
    }

    @Override
    public int hashCode() {
        return this.numerator.hashCode() + 3 * this.denominator.hashCode();
    }

    @Override
    public String toString() {
        if (this.denominator.equals(BigInteger.ONE)) {
            return this.numerator.toString();
        } else {
            return this.numerator.toString() + "/" + this.denominator.toString();
        }
    }

    @Override
    public String export(final Export_Util eu) {
        if (this.denominator.equals(BigInteger.ONE)) {
            return eu.escape(this.numerator.toString());
        } else {
            return eu.fraction(this.numerator.toString(), this.denominator.toString());
        }
    }
}
