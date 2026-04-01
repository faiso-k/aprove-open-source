package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Generates different types of polynomial interpretations for defined and
 * constant function symbols.
 */
public class GInterpretationModeDual<C extends GPolyCoeff> extends GInterpretationMode<C> {

    private final Set<FunctionSymbol> definedSymbols;
    private final GInterpretationMode<C> formConstant;
    private final GInterpretationMode<C> formDefined;

    public GInterpretationModeDual(Set<FunctionSymbol> definedSymbols,
            GInterpretationMode<C> formConstant, GInterpretationMode<C> formDefined) {
        this.definedSymbols = definedSymbols;
        this.formConstant = formConstant;
        this.formDefined = formDefined;
    }

    @Override
    public OrderPoly<C> getPolynomial(GInterpretation<C> interp,
            FunctionSymbol fs, List<OrderPoly<C>> variables) {
        if (this.definedSymbols.contains(fs)) {
            return this.formDefined.getPolynomial(interp, fs, variables);
        } else {
            return this.formConstant.getPolynomial(interp, fs, variables);
        }
    }

}
