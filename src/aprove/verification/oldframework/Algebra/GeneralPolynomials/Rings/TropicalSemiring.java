package aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * The tropical semiring, a.k.a. min-plus algebra.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class TropicalSemiring extends ExoticAlgebra<TropicalInt> {

    private static TropicalSemiring INSTANCE = null;

    private TropicalSemiring() {}

    public static TropicalSemiring create() {
        if (TropicalSemiring.INSTANCE == null) {
            TropicalSemiring.INSTANCE = new TropicalSemiring();
        }
        return TropicalSemiring.INSTANCE;
    }

    @Override
    public TropicalInt one() {
        return TropicalInt.ONE;
    }

    @Override
    public TropicalInt zero() {
        return TropicalInt.ZERO;
    }
}