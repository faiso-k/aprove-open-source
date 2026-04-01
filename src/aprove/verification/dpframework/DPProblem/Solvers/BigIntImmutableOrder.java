/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.Solvers;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * Give information about the relation of any given BigIntImmutable to 0.
 * Use BigInteger's signum().
 * @author cotto
 */
public class BigIntImmutableOrder implements CoeffOrder<BigIntImmutable> {
    /**
     * @param object The BigIntImmutable object to compare with 0.
     * @return see BigInteger.signum().
     */
    @Override
    public int signum(final BigIntImmutable object) {
        return object.getBigInt().signum();
    }

    @Override
    public boolean equal(final BigIntImmutable first, final BigIntImmutable second) {
        return first.getBigInt().compareTo(second.getBigInt()) == 0;
    }

    @Override
    public boolean isGreater(final BigIntImmutable first, final BigIntImmutable second) {
        return first.getBigInt().compareTo(second.getBigInt()) > 0;
    }

    @Override
    public boolean isGreaterOrEqual(final BigIntImmutable first,
            final BigIntImmutable second) {
        return first.getBigInt().compareTo(second.getBigInt()) >= 0;
    }

}
