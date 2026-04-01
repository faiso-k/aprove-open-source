package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * ax + by + c.
 */
public class GInterpretationModeLinear<C extends GPolyCoeff> extends GInterpretationMode<C> {

    private final OPCRange<C> coeffRange;
    private final OPCRange<C> constantRange;

    public GInterpretationModeLinear() {
        this.coeffRange = null;
        this.constantRange = null;
    }

    /**
     * Uses constantRange for the constant part and coeffRange for coefficients.
     * Null designates the default range.
     */
    public GInterpretationModeLinear(OPCRange<C> coeffRange, OPCRange<C> constantRange) {
        this.coeffRange = coeffRange;
        this.constantRange = constantRange;
    }
    @Override
    public OrderPoly<C> getPolynomial(GInterpretation<C> interp,
            FunctionSymbol fs, List<OrderPoly<C>> variables) {
        GPolyVar var = interp.getNextCoeff(this.constantRange);
        OrderPoly<C> inter = interp.factory.buildFromInnerVariable(var);

        for (OrderPoly<C> variable : variables) {
            var = interp.getNextCoeff(this.coeffRange);
            OrderPoly<C> coeffI = interp.factory.buildFromInnerVariable(var);
            inter = interp.getFactory().plus(inter,
                    interp.getFactory().times(coeffI, variable));
        }
        return inter;
    }

}
