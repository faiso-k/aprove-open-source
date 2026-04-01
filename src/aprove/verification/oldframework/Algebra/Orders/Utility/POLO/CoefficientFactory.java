package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 */
public class CoefficientFactory implements VariableFactory {

  public final Set forbiddenNames;
  public int index;
  public static final String prefix = "a_";

  private CoefficientFactory(Set forbiddenNames) {
    this.forbiddenNames = forbiddenNames;
    this.reset();
  }

  public static CoefficientFactory create(Set forbiddenNames) {
    return new CoefficientFactory(forbiddenNames);
  }


  public Set getForbiddenNames() {
    return this.forbiddenNames;
}

@Override
public String nextName() {
    String name;
    do {
      ++this.index;
      name = CoefficientFactory.prefix + this.index;
    } while (this.forbiddenNames.contains(name));

    return name;
  }

  @Override
public Polynomial nextVariable() {
    return Polynomial.createVariable(this.nextName());
  }

  public void reset() {
    this.index = 0;
  }

}
