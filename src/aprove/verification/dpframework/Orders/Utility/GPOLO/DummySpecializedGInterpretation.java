package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

public class DummySpecializedGInterpretation implements
        SpecializedGInterpretation {

    private final static DummySpecializedGInterpretation INSTANCE =
        new DummySpecializedGInterpretation();

    private DummySpecializedGInterpretation() {}

    public static DummySpecializedGInterpretation create() {
        return DummySpecializedGInterpretation.INSTANCE;
    }

    @Override
    public <C extends GPolyCoeff> Set<OrderPolyConstraint<C>> getStrongMonotonicityConstraints(
            GInterpretation<C> interp) {
        throw new UnsupportedOperationException();
    }

    @Override
    public <C extends GPolyCoeff> boolean isStronglyMonotonic(
            GInterpretation<C> interp, OrderPoly<C> poly, GPolyVar var) {
        throw new UnsupportedOperationException();
    }

}
