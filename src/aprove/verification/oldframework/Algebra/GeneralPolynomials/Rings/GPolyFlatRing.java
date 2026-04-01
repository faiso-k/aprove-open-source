package aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings;

import java.util.*;

import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * A (semi-) ring on flat representations of Polynomials using coefficients
 * of type C and variables of type V. Whether its instances represent actual
 * rings or not depends on the type of the coefficient ring plugged into them.
 * @author cotto
 * @version $Id$
 */
public interface GPolyFlatRing<C, V extends GPolyVar> extends Ring<Map<GMonomial<V>, C>> {

    Semiring<C> getRing();
    CMonoid<GMonomial<V>> getMonoid();
}
