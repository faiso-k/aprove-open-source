package aprove.verification.dpframework.DPProblem.Solvers;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class TropicalIntOrder extends ExoticIntOrder<TropicalInt> {

    private static TropicalIntOrder INSTANCE = null;

    private TropicalIntOrder() {}

    public static TropicalIntOrder create() {
        if (TropicalIntOrder.INSTANCE == null) {
            TropicalIntOrder.INSTANCE = new TropicalIntOrder();
        }
        return TropicalIntOrder.INSTANCE;
    }
}