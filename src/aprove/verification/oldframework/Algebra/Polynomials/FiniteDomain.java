package aprove.verification.oldframework.Algebra.Polynomials;

import java.math.*;
import java.util.*;

import immutables.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 *
 * docu-guess (fuhs):
 * Encodes variable \in \[lowerBound, upperBound\].
 */
public class FiniteDomain implements Immutable {

  public final FDBoundary lowerBound;
  public final FDBoundary upperBound;
  public final String variable;

  private FiniteDomain(String variable, FDBoundary lowerBound, FDBoundary upperBound) {
    this.lowerBound = lowerBound;
    this.upperBound = upperBound;
    this.variable = variable;
  }

  public static FiniteDomain create(String variable, FDBoundary lowerBound, FDBoundary upperBound) {
    return new FiniteDomain(variable, lowerBound, upperBound);
  }

    /**
     * docu-guess (fuhs):
     * @param values mapping [String -> BigIntegerInterval], maps variables to their
     *  minimum and maximum values
     * @return the minimum value this.variable can take given values
     */
  public BigInteger getMin(Map<String, BigIntegerInterval> values) throws ArithmeticException,NotSolveableException {
    return this.lowerBound.min(values);
  }

    /**
     * docu-guess (fuhs):
     * @param values mapping [String -> BigIntegerInterval], maps variables to their
     *  minimum and maximum values
     * @return the maximum value this.variable can take given values
     */
  public BigInteger getMax(Map<String, BigIntegerInterval> values) throws ArithmeticException,NotSolveableException {
    return this.upperBound.max(values);
  }

  @Override
public String toString() {
    StringBuilder buffer = new StringBuilder(this.variable);

    buffer.append(" in [");
    buffer.append(this.lowerBound.toString());
    buffer.append(", ");
    buffer.append(this.upperBound.toString());
    buffer.append("]");

    return buffer.toString();
  }

  /**
   * Converts this to a FiniteDomain that represents the strict version
   * of the underlying (GE) constraint. This is done by
   * - changeLowerBound == true:  incrementing
   * - changeLowerBound == false: decrementing
   * the numerator of the specified bound.
   *
   * This is a conversion which -- when performed on all of the FiniteDomains
   * that correspond to some SimplePolyConstraint of type GE -- is equivalent
   * to making said SimplePolyConstraint strict (GT).
   *
   * @param changeLowerBound true -> change the lower bound of this,
   *  false -> change the upper bound of this
   * @return
   */
  public FiniteDomain toStrict(boolean changeLowerBound) {
      if (changeLowerBound) {
          SimplePolynomial newLowerBoundNumerator;
          newLowerBoundNumerator = this.lowerBound.numerator.plus(SimplePolynomial.ONE);
          FDBoundary newLowerBound;
          newLowerBound = FDBoundary.create(newLowerBoundNumerator,
                  this.lowerBound.denominator, this.lowerBound.exponent);
          return new FiniteDomain(this.variable, newLowerBound, this.upperBound);
      }
      else {
          SimplePolynomial newUpperBoundNumerator;
          newUpperBoundNumerator = this.upperBound.numerator.minus(SimplePolynomial.ONE);
          FDBoundary newUpperBound;
          newUpperBound = FDBoundary.create(newUpperBoundNumerator,
                  this.upperBound.denominator, this.upperBound.exponent);
          return new FiniteDomain(this.variable, this.lowerBound, newUpperBound);
      }
  }

  /**
   * Converts this to a FiniteDomain that represents the non-strict version
   * of the underlying (GT) constraint. This is done by
   * - changeLowerBound == true:  decrementing
   * - changeLowerBound == false: incrementing
   * the numerator of the specified bound.
   *
   * This is a conversion which -- when performed on all of the FiniteDomains
   * that correspond to some SimplePolyConstraint of type GT -- is equivalent
   * to making said SimplePolyConstraint non-strict (GE).
   *
   * @param changeLowerBound true -> change the lower bound of this,
   *  false -> change the upper bound of this
   * @return
   */
  public FiniteDomain toNonStrict(boolean changeLowerBound) {
      if (changeLowerBound) {
          SimplePolynomial newLowerBoundNumerator;
          newLowerBoundNumerator = this.lowerBound.numerator.minus(SimplePolynomial.ONE);
          FDBoundary newLowerBound;
          newLowerBound = FDBoundary.create(newLowerBoundNumerator,
                  this.lowerBound.denominator, this.lowerBound.exponent);
          return new FiniteDomain(this.variable, newLowerBound, this.upperBound);
      }
      else {
          SimplePolynomial newUpperBoundNumerator;
          newUpperBoundNumerator = this.upperBound.numerator.plus(SimplePolynomial.ONE);
          FDBoundary newUpperBound;
          newUpperBound = FDBoundary.create(newUpperBoundNumerator,
                  this.upperBound.denominator, this.upperBound.exponent);
          return new FiniteDomain(this.variable, this.lowerBound, newUpperBound);
      }
  }
}
