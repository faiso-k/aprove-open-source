package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

/**
 * A functional integer expression is either an integer function expression or an integer variable.
 * @author cryingshadow
 * @version $Id$
 */
public interface FunctionalIntegerExpression
extends IntegerExpression, FunctionalArithmeticExpression, SMTSExpressible<SInt> {

    @Override
    FunctionalIntegerExpression negate();

}
