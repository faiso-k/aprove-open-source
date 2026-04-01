package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 */
public interface VariableFactory {

  public Polynomial nextVariable();
  public String nextName();

}
