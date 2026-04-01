package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 */
public class TemplateVariableFactory implements VariableFactory {

  public static final String TEMPLATE_VARIABLE_NAME = "v";
  public static final Polynomial TEMPLATE_VARIABLE = Polynomial.createVariable(TemplateVariableFactory.TEMPLATE_VARIABLE_NAME);

  private TemplateVariableFactory() {
  }

  public static TemplateVariableFactory create() {
    return new TemplateVariableFactory();
  }

  @Override
public String nextName() {
    return TemplateVariableFactory.TEMPLATE_VARIABLE_NAME;
  }

  @Override
public Polynomial nextVariable() {
    return TemplateVariableFactory.TEMPLATE_VARIABLE;
  }

}
