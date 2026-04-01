package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.GInterpretationModeStronglyLinear.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Generates linear or quadratic or 'degree' restricted polynomials.
 *
 * For defined symbols: Polynomial of order degree.
 * For constructor symbols: Polynomial of order 1 with coefficients 1.
 */
public class GInterpretationModeRestricted<C extends GPolyCoeff> extends GInterpretationMode<C> {

    private final Set<FunctionSymbol> definedSymbols;

    private final GInterpretationMode<C> gimConstants;
    private final GInterpretationMode<C> gimDefined;

    public GInterpretationModeRestricted(int degree, Set<FunctionSymbol> definedSymbols) {
        this.definedSymbols = definedSymbols;

        this.gimConstants = new GInterpretationModeStronglyLinear<C>(ConstantPart.VAR);
        this.gimDefined = new GInterpretationModeDegree<C>(degree);
    }

    @Override
    public OrderPoly<C> getPolynomial(GInterpretation<C> interp,
            FunctionSymbol fs, List<OrderPoly<C>> variables) {
        if (this.definedSymbols.contains(fs)) {
            return this.gimDefined.getPolynomial(interp, fs, variables);
        } else {
            return this.gimConstants.getPolynomial(interp, fs, variables);
        }
    }

}
