package aprove.verification.oldframework.SMT;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

/**
 * Can be turned into a T-valued S-expression for SMTLIB.
 * @author cryingshadow
 * @version $Id$
 * @param <T> The value type of the resulting S-expression.
 */
public interface SMTSExpressible<T extends Sort> {

    /**
     * @return A T-valued SMTLIB S-Expression corresponding to this.
     */
    SMTExpression<T> toSMTExp();

}
