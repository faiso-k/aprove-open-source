package aprove.verification.oldframework.Algebra.Polynomials;

import java.util.*;

import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Verifier.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 *
 * (Thiemann guessed):
 * A PolyConstraint is encoded as a poly >= / > / = 0
 * To see what variables are all-quantified and what variables we have to look at,
 * PolyConstraints are usually put into a Map, where each constraint is mapped
 * to the set of bound variables! (Coefficients are variables internally)
 */
public class PolyConstraint extends AbstractConstraint {

  private PolyConstraint(Polynomial polynomial, int type) {
    super(polynomial, Polynomial.ZERO, type);
  }

  public static PolyConstraint create(Polynomial polynomial, int type) {
    return new PolyConstraint(polynomial, type);
  }

  public Polynomial getPolynomial() {
    return (Polynomial) this.left;
  }

  public void setPolynomial(Polynomial p) {
      this.left = p;
  }

  /**
   * Performs some simple checks if this constraint is satisfiable.
   *
   * @return true if this constraint is satisfiable, false otherwise
   */
  public boolean isSatisfiable() {
    if ((this.type == AbstractConstraint.GR) && (this.getPolynomial().allNegative())) {
        return false;
    }

    if (this.getPolynomial().isConstant()) {
      int value = (this.getPolynomial().isEmpty()) ? 0 : ((Monomial) this.getPolynomial().getFirst()).coeff;

      switch (this.type) {
        case EQ :
          if (value != 0) {
            return false;
        }
          break;
        case GE :
          if (value < 0) {
            return false;
        }
          break;
        case GR :
          if (value <= 0) {
            return false;
        }
          break;
      }
    }

    return true;
  }

  /**
   * Performs some simple checks if this constraint is valid.
   *
   * @return true if this constraint is valid, false otherwise
   */
  public boolean isValid() {
    if ((this.type == AbstractConstraint.GE) && (this.getPolynomial().allPositive())) {
        return true;
    }

    if (this.getPolynomial().isConstant()) {
      int value = (this.getPolynomial().isEmpty()) ? 0 : ((Monomial) this.getPolynomial().getFirst()).coeff;

      switch (this.type) {
        case EQ :
          if (value == 0) {
            return true;
        }
        case GE :
          if (value >= 0) {
            return true;
        }
        case GR :
          if (value > 0) {
            return true;
        }
      }
    }

    return false;
  }

  public boolean satisfiedBy(State state) {
    long value = this.getPolynomial().evaluate(state);

    switch (this.getType()) {
      case EQ :
        if (value != 0) {
            return false;
        }
        break;
      case GE :
        if (value < 0) {
            return false;
        }
        break;
      case GR :
        if (value <= 0) {
            return false;
        }
        break;
    }

    return true;
  }

    private static final Integer ONE = 1;

    // docu-guess (fuhs): a reduced version of SimplePolyConstraintSimplifier
    public void simplifyAndAdd(Collection<PolyConstraint> constraints) {
        if ((((this.type == AbstractConstraint.EQ) || (this.type == AbstractConstraint.GE)) && (this.getPolynomial().allNegative()))
                || ((this.type == AbstractConstraint.EQ) && (this.getPolynomial().allPositive()))) {
            for (Monomial m : this.getPolynomial()) {

                SortedMap<String, Integer> exponents = new TreeMap<String, Integer>();
                for (String s : m.exponents.keySet()) {
                    exponents.put(s, PolyConstraint.ONE);
                }

                constraints.add(
                        PolyConstraint.create(Polynomial.create(Monomial.create(1, exponents)), AbstractConstraint.EQ));
            }

        } else {
            constraints.add(this);
        }
    }

}
