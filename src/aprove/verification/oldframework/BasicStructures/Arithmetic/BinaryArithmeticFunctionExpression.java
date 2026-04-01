package aprove.verification.oldframework.BasicStructures.Arithmetic;

import aprove.verification.oldframework.BasicStructures.*;

/**
 * Binary arithmetic expressions offer an arithmetic operation.
 * @author cryingshadow
 * @version $Id$
 */
public interface BinaryArithmeticFunctionExpression extends ArithmeticFunctionExpression, BinaryExpression {

    @Override
    default int getArity() {
        return 2;
    }

}
