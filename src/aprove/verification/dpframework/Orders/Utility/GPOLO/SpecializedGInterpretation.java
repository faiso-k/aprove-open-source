package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Used by GInterpretation to provide specialized constraints differing for
 * various Semirings
 *
 * Instances are provided to {@link GInterpretation} by the
 * getSpecializedGInterpretation method of {@link Semiring}.
 *
 */
public interface SpecializedGInterpretation {

    public <C extends GPolyCoeff> Set<OrderPolyConstraint<C>>
            getStrongMonotonicityConstraints(GInterpretation<C> interp);

    public <C extends GPolyCoeff> boolean isStronglyMonotonic(
            GInterpretation<C> interp,
            OrderPoly<C> poly, GPolyVar var);

}
