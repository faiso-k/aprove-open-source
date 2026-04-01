package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Generates strongly linear polynomials,
 *
 * i.e. linear polynomials, where all variables of coefficient 1.
 */
public class GInterpretationModeStronglyLinear<C extends GPolyCoeff> extends GInterpretationMode<C> {

    private final ConstantPart constantPart;

    /**
     * Values for the constant part of the polynomial interpretation
     */
    public static enum ConstantPart {
        /**
         * Constant part is always zero
         */
        ZERO,

        /**
         * Constant part is always one
         */
        ONE,

        /**
         * Constant part is 1 + x, where x is a fresh variable.
         *
         * This is called 'Strongly Linear' in 'Automated Complexity Analysis
         * Based on the Dependency Pair Method' by Hirokawa and Moser
         */
        ONE_PLUS_VAR,

        /**
         * Constant part is x, where x is a fresh variable
         */
        VAR,
    }

    public GInterpretationModeStronglyLinear(ConstantPart constantPart) {
        this.constantPart = constantPart;
    }

    @Override
    public OrderPoly<C> getPolynomial(GInterpretation<C> interp,
            FunctionSymbol fs, List<OrderPoly<C>> variables) {
        OrderPoly<C> sum;
        switch (this.constantPart) {
            case ZERO:
                sum = this.getZeroMonomial(interp);
                break;

            case ONE:
                sum = this.getOneMonomial(interp);
                break;

            case ONE_PLUS_VAR:
                sum = interp.factory.plus(
                        this.getOneMonomial(interp), this.getFreshVariableMonomial(interp, fs));
                break;

            case VAR:
                sum = this.getFreshVariableMonomial(interp, fs);
                break;

            default:
                if (Globals.useAssertions) {
                    assert(false) : "Invalid constant part selected:" + this.constantPart;
                }
                throw new RuntimeException("Invalid constant part selected: " + this.constantPart);
        }
        for (OrderPoly<C> var : variables) {
            sum = interp.factory.plus(sum, var);
        }
        return sum;
    }

}
