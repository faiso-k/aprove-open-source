package aprove.verification.complexity.Utility;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

public class GPolyTools {

    public static <C extends GPolyCoeff> String format(
            GInterpretation<C> interp, OrderPoly<C> poly) {
        return poly.exportFlatDeep(
                interp.getFvInner(), interp.getFvOuter(), new PLAIN_Util());
    }
}
