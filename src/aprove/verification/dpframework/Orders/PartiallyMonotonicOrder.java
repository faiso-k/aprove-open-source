package aprove.verification.dpframework.Orders;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * A PartiallyMonotonicOrder is an order on terms that may be monotonic wrt
 * &gt; in all, some, or none of its arguments. It can tell about
 * monotonicity for function symbols and their arguments.
 *
 * Note that this property does not coincide with the question whether the
 * corresponding argument is filtered away. For instance, the order based on
 * the polynomial interpretation over the naturals that interprets a binary
 * symbol f by the product of its arguments does not filter away any argument,
 * but it is not (strongly) monotonic in any of its argument.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public interface PartiallyMonotonicOrder extends Order<TRSTerm> {

    /**
     * @param f - a function symbol that must be in the underlying signature
     *  of the order; non-null
     * @param i - an argument position of f (in {0, ..., f.getArity()})
     * @return whether f is guaranteed to be monotonic in its i-th argument
     *  (false negatives may occur)
     */
    boolean fIsMonotonicInArg(FunctionSymbol f, int i);
}
