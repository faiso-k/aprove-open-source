package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.*;

/**
 * IntegerExpressions offer an export to an SMTLIB expression over the theory of integers.
 * @author cryingshadow
 * @version $Id$
 */
public interface IntegerExpression extends ArithmeticExpression {

    @Override
    Set<? extends IntegerVariable> getVariables();

}
