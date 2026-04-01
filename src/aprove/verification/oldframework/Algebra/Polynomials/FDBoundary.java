package aprove.verification.oldframework.Algebra.Polynomials;

import java.math.*;
import java.util.*;

import immutables.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 *
 * FDBoundary encodes an expression of the form
 * (numerator / denominator)^(1/exponent)
 * where denominator == null encodes that the denominator is one.
 */
public class FDBoundary implements Immutable {

  public final SimplePolynomial denominator;
  public final int exponent;
  public final SimplePolynomial numerator;
  public final ImmutableMap<String, Integer> variables; // how often does each variable occur in this?
                                                        // (disregarding their powers)

    private FDBoundary(SimplePolynomial numerator, SimplePolynomial denominator, int exponent) {
        this.denominator = denominator;
        this.exponent = exponent;
        this.numerator = numerator;
        Map<String, Integer> variables = new LinkedHashMap<String, Integer>();

        this.numerator.countIndefinites(variables);
        if (this.denominator != null) {
            this.denominator.countIndefinites(variables);
        }
        this.variables = ImmutableCreator.create(variables);
    }

  public static FDBoundary create(SimplePolynomial numerator) {
    return new FDBoundary(numerator, null, 1);
  }

  public static FDBoundary create(
    SimplePolynomial numerator,
    SimplePolynomial denominator,
    int exponent) {

    if (exponent == 0) {
        throw new IllegalArgumentException();
    }

    if ((denominator != null)
      && (denominator.isConstant())
      && (numerator.isZero())) {
      denominator = null;
      exponent = 1;
    }

    return new FDBoundary(numerator, denominator, exponent);
  }

  @Override
public String toString() {
    StringBuilder buffer = new StringBuilder();

    if (this.exponent != 1) {
        buffer.append("(");
    }

    if (this.denominator == null) {
        buffer.append(this.numerator.toString());
    } else {
      if ((!(this.numerator.isConstant())) && (!(this.numerator.isIndefinite()))) {
        buffer.append("(");
    }

      buffer.append(this.numerator.toString());

      if ((!(this.numerator.isConstant())) && (!(this.numerator.isIndefinite()))) {
        buffer.append(")");
    }

      buffer.append(" / ");

      if ((!(this.denominator.isConstant())) && (!(this.denominator.isIndefinite()))) {
        buffer.append("(");
    }

      buffer.append(this.denominator.toString());

      if ((!(this.denominator.isConstant())) && (!(this.denominator.isIndefinite()))) {
        buffer.append(")");
    }
    }

    if (this.exponent != 1) {
      buffer.append(")^(1/");
      buffer.append(this.exponent);
      buffer.append(")");
    }

    return buffer.toString();
  }

    /**
     * docu-guess (fuhs):
     * @param values mapping [String -> IntegerInterval], maps variables
     *  to their minimum and maximum values
     * @return the maximum value this can take given values.
     */
  public BigInteger max(Map<String, BigIntegerInterval> values) throws ArithmeticException,NotSolveableException {
    BigInteger value = this.numerator.max(values);
    // a^n*denom <= numerate cannot be fulfilled as a^n*denom is >= 0
    if (value.signum() < 0) {
        throw new NotSolveableException();
    }

    if (this.denominator != null) {
      BigInteger denom = this.denominator.min(values);

      if (denom.signum() != 0) {
        value = value.divide(denom);
    } else {
        // always fulfilled
        throw new ArithmeticException();
    }
    }

    if (this.exponent != 1) {
        value = BigInteger.valueOf((long) Math.floor(Math.pow(value.doubleValue(), 1.0 / this.exponent)));
    }

    return value;
  }

    /**
     * TODO work on BigInteger natively also for roots
     *
     * docu-guess (fuhs):
     * @param values mapping [String -> IntegerInterval], maps variables
     *  to their minimum and maximum values
     * @return the minimum value this can take given values.
     */
  public BigInteger min(Map<String, BigIntegerInterval> values) throws ArithmeticException,NotSolveableException {
    BigInteger value = this.numerator.min(values);
    if (value.signum() <= 0) {
        // a^n*denom >= numerate always fulfilled as a^n*denom is >= 0
        return BigInteger.ZERO; // no restrictions here, perhaps return ArithException
    }

    if (this.denominator != null) {
      BigInteger denom = this.denominator.max(values);
      if (denom.signum() != 0) {
        value = value.divide(denom);
    } else {
        // a^n * denom = 0 can not be >= numerator (> 0)
        throw new NotSolveableException();
    }
    }

    if (this.exponent != 1) {
        value = BigInteger.valueOf((long) Math.ceil(Math.pow(value.doubleValue(), 1.0 / this.exponent)));
    }

    return value;
  }

}
