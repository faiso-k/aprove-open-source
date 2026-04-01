package aprove.verification.oldframework.Algebra.Polynomials;

import immutables.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 */
public class IntegerInterval implements Immutable {

  public final int max;
  public final int min;

  public IntegerInterval(int min, int max) {
    this.min = min;
    this.max = max;
  }

  @Override
public String toString() {
    StringBuffer b = new StringBuffer("[");
    b.append(this.min);
    b.append(",");
    b.append(this.max);
    b.append("]");

    return b.toString();
  }

}
