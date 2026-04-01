package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.math.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import immutables.*;

/**
 * A simple implementation of BigRationals.
 * <p>
 * Invariants:
 * <ul>
 * <li>Zero is represented by 0/1.</li>
 * <li>The {@code denominator} is always strictly greater zero.</li>
 * <li>The {@code numerator} and {@code denominator} have no common divisor.</li>
 * </p>
 */
public final class BigRational implements Immutable, Exportable, Comparable<BigRational> {

    public static final BigRational ZERO = new BigRational(0, 1);
    public static final BigRational ONE = new BigRational(1, 1);
    public static final BigRational TWO = new BigRational(2, 1);
    public static final BigRational MINUSONE = new BigRational(-1, 1);

    public final BigInteger numerator;
    public final BigInteger denominator;

    public BigRational(final BigInteger value) {
        this(value, BigInteger.ONE);
    }

    public BigRational(final long value) {
        this(value, 1);
    }

    /**
     * If the denominator is zero, an {@link ArithmeticException} will be
     * thrown.
     * @param numerator
     * @param denominator
     */
    public BigRational(BigInteger numerator, BigInteger denominator) {
        if (BigInteger.ZERO.equals(denominator)) {
            throw new ArithmeticException("Denominator must not be zero.");
        }
        if (denominator.signum() < 0) {
            denominator = denominator.abs();
            numerator = numerator.negate();
        }
        if (BigInteger.ZERO.equals(numerator)) {
            this.numerator = BigInteger.ZERO;
            this.denominator = BigInteger.ONE;
        } else {
            BigInteger divisor = numerator.gcd(denominator);
            this.numerator = numerator.divide(divisor);
            this.denominator = denominator.divide(divisor);
        }
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.denominator == null ? 0 : this.denominator.hashCode());
        result = prime * result + (this.numerator == null ? 0 : this.numerator.hashCode());
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        BigRational other = (BigRational) obj;
        if (this.denominator == null) {
            if (other.denominator != null) {
                return false;
            }
        } else if (!this.denominator.equals(other.denominator)) {
            return false;
        }
        if (this.numerator == null) {
            if (other.numerator != null) {
                return false;
            }
        } else if (!this.numerator.equals(other.numerator)) {
            return false;
        }
        return true;
    }

    public BigRational(final long numerator, final long denominator) {
        this(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator));
    }

    public static BigRational valueOf(final BigDecimal n) {
        int scale = n.scale();
        BigInteger unscaled = n.unscaledValue();
        BigInteger factor = BigInteger.valueOf(10).pow(Math.abs(scale));
        if (scale < 0) {
            return new BigRational(unscaled.multiply(factor));
        } else {
            return new BigRational(unscaled, factor);
        }
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public int compareTo(final BigRational o) {
        BigInteger left = this.numerator.multiply(o.denominator);
        BigInteger right = o.numerator.multiply(this.denominator);
        return left.compareTo(right);
    }

    public BigRational add(final BigRational o) {
        BigInteger numerator = this.numerator.multiply(o.denominator).add(o.numerator.multiply(this.denominator));
        BigInteger denominator = this.denominator.multiply(o.denominator);
        return new BigRational(numerator, denominator);
    }

    public BigRational subtract(final BigRational o) {
        BigInteger numerator = this.numerator.multiply(o.denominator).subtract(o.numerator.multiply(this.denominator));
        BigInteger denominator = this.denominator.multiply(o.denominator);
        return new BigRational(numerator, denominator);
    }

    public BigRational multiply(final BigRational o) {
        return new BigRational(this.numerator.multiply(o.numerator), this.denominator.multiply(o.denominator));
    }

    public BigRational divide(final BigRational o) {
        return new BigRational(this.numerator.multiply(o.denominator), this.denominator.multiply(o.numerator));
    }

    public BigRational negate() {
        return new BigRational(this.numerator.negate(), this.denominator);
    }

    public BigRational abs() {
        return new BigRational(this.numerator.abs(), this.denominator);
    }

    public BigRational pow(final int exponent) {
        return new BigRational(this.numerator.pow(exponent), this.denominator.pow(exponent));
    }

    public int signum() {
        return this.numerator.signum();
    }

    public SMTLIBRatValue toSMTLIBRatValue() {
        return SMTLIBRatConstant.create(this.numerator, this.denominator);
    }

    @Override
    public String export(final Export_Util eu) {
        if (this.numerator.equals(BigInteger.ZERO)) {
            return "(0)";
        }
        if (this.denominator.equals(BigInteger.ONE)) {
            return "(" + this.numerator.toString() + ")";
        }
        return "(" + this.numerator.toString() + "/" + this.denominator.toString() + ")";
    }
}
