/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.Solvers;

import java.math.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * Give information about the relation of some MbyN number to 0.
 * @author cotto
 */
public class MbyNOrder implements CoeffOrder<MbyN> {
    /**
     * @return 0 for MbyN == 0, a value less than 0 for MbyN < 0, a value larger
     * than 0 for MbyN > 0.
     * @param object the MbyN to compare.
     */
    @Override
    public int signum(final MbyN object) {
        return object.getPair().x.signum();
    }

    @Override
    public boolean equal(final MbyN first, final MbyN second) {
        return first.equals(second);
    }

    @Override
    public boolean isGreater(final MbyN first, final MbyN second) {
        BigInteger commonDenom = first.getDenominator().multiply(second.getDenominator());
        BigInteger firstInt = first.getNumerator().multiply(commonDenom).divide(first.getDenominator());
        BigInteger secondInt = second.getNumerator().multiply(commonDenom).divide(second.getDenominator());
        boolean result = firstInt.compareTo(secondInt) > 0;
        return result;
    }

    @Override
    public boolean isGreaterOrEqual(final MbyN first, final MbyN second) {
        return this.equal(first, second) || this.isGreater(first, second);
    }

}
