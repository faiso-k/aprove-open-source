package aprove.verification.dpframework.DPProblem.Solvers;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ArcticIntOrder extends ExoticIntOrder<ArcticInt> {

    private static ArcticIntOrder INSTANCE = null;

    private ArcticIntOrder() {}

    public static ArcticIntOrder create() {
        if (ArcticIntOrder.INSTANCE == null) {
            ArcticIntOrder.INSTANCE = new ArcticIntOrder();
        }
        return ArcticIntOrder.INSTANCE;
    }
}
