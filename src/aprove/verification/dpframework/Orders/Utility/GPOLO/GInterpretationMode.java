package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;

public abstract class GInterpretationMode<C extends GPolyCoeff> {

    /**
     * @param variables One variable for each argument of the function symbol.
     */
    public abstract OrderPoly<C> getPolynomial(
            GInterpretation<C> interp,
            FunctionSymbol fs,
            List<OrderPoly<C>> variables);

    public static <C extends GPolyCoeff> GInterpretationMode<C> createFromLegacy(int degree, int maxSimpleDegree) {
        if (degree == GInterpretation.LINEAR) {
            return new GInterpretationModeLinear<C>();
        } else if (degree == GInterpretation.SIMPLE) {
            return new GInterpretationModeSimple<C>(maxSimpleDegree);
        } else if (degree == GInterpretation.SIMPLE_MIXED) {
            return new GInterpretationModeSimpleMixed<C>(maxSimpleDegree);
        } else {
            return new GInterpretationModeDegree<C>(degree);
        }
    }

    /**
     * Returns a OrderPoly<C> representing 0
     */
    protected OrderPoly<C> getZeroMonomial(GInterpretation<C> interp) {
        return interp.factory.buildFromCoeff(
                    interp.factory.getInnerFactory().buildFromCoeff(
                            interp.ring.zero()));
    }

    /**
     * Returns a OrderPoly<C> representing 1
     */
    protected OrderPoly<C> getOneMonomial(GInterpretation<C> interp) {
        return interp.factory.getOne();
    }

    protected OrderPoly<C> getFreshVariableMonomial(
            GInterpretation<C> interp, FunctionSymbol fs) {
        return interp.getNextCoeffOrderPoly(fs);
    }

}
