package aprove.verification.oldframework.BasicStructures.Arithmetic;

/**
 * Functional expressions are either functions or variables.
 * @author cryingshadow
 * @version $Id$
 */
public interface FunctionalArithmeticExpression extends ArithmeticExpression {

    /**
     * @return -this.
     */
    FunctionalArithmeticExpression negate();

}
