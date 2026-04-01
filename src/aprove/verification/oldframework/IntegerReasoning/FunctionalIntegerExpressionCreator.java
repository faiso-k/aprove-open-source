package aprove.verification.oldframework.IntegerReasoning;

import java.math.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * Creator for functional integer expressions.
 * @author cryingshadow
 * @version $Id$
 */
public interface FunctionalIntegerExpressionCreator {

    /**
     * @param value The value of the constant.
     * @return A constant with the specified value.
     */
    IntegerConstant constant(BigInteger value);

    /**
     * @param op The operation.
     * @param args The arguments.
     * @return A compound expression with the specified operation and arguments.
     */
    CompoundFunctionalIntegerExpression operation(ArithmeticOperationType op, FunctionalIntegerExpression... args);

    /**
     * @param name The name of the variable.
     * @return A variable with the specified name.
     */
    IntegerVariable variable(String name);

}
