package aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * The arctic semiring, a.k.a. max-plus algebra.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ArcticSemiring extends ExoticAlgebra<ArcticInt> {

    private static ArcticSemiring INSTANCE = null;

    private ArcticSemiring() {}

    public static ArcticSemiring create() {
        if (ArcticSemiring.INSTANCE == null) {
            ArcticSemiring.INSTANCE = new ArcticSemiring();
        }
        return ArcticSemiring.INSTANCE;
    }

    @Override
    public ArcticInt one() {
        return ArcticInt.ONE;
    }

    @Override
    public ArcticInt zero() {
        return ArcticInt.ZERO;
    }
}
