/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.Solvers;

import java.math.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * Give information about the relation of some PoT number to 0.
 * @author cotto
 */
public class PoTOrder implements CoeffOrder<PoT> {
    /**
     * @return 0 for PoT == 0, a value less than 0 for PoT < 0, a value larger
     * than 0 for PoT > 0.
     * @param object the PoT to compare.
     */
    @Override
    public int signum(final PoT object) {
        return object.getPair().x.signum();
    }

    @Override
    public boolean equal(final PoT first, final PoT second) {
        return first.equals(second);
    }

    @Override
    public boolean isGreater(final PoT first, final PoT second) {
        BigInteger commonDenom = first.getDenominator().multiply(second.getDenominator());
        return first.getNumerator().multiply(commonDenom).compareTo(second.getNumerator().multiply(commonDenom)) > 0;
    }

    @Override
    public boolean isGreaterOrEqual(final PoT first, final PoT second) {
        return this.equal(first, second) || this.isGreater(first, second);
    }

}
