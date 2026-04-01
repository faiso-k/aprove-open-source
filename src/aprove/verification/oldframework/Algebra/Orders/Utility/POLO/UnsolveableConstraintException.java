package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * This Exception will be thrown by POLO related methods if an unsolveable polynomial constraint
 * will be detected.
 *
 * @author Andreas Capellmann
 * @version $Id$
 */
public class UnsolveableConstraintException extends Exception {

  public UnsolveableConstraintException() {
    super("Unsolveable constraint detected!");
  }

  public UnsolveableConstraintException(PolyConstraint constraint) {
    super("Unsolveable constraint detected: " + constraint);
  }

    public UnsolveableConstraintException(SimplePolyConstraint constraint) {
        super("Unsolveable constraint detected: " + constraint);
    }

}
