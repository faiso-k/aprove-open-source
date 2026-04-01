package aprove.verification.dpframework.DPProblem.Solvers;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ExoticIntOrder<T extends ExoticInt<T>> implements CoeffOrder<T> {

    @Override
    public boolean equal(T first, T second) {
        return first.equals(second);
    }

    @Override
    public boolean isGreater(T first, T second) {
        return first.isGreater(second);
    }

    @Override
    public boolean isGreaterOrEqual(T first, T second) {
        return first.isGreaterOrEqual(second);
    }

    @Override
    public int signum(T object) {
        return object.signum();
    }
}