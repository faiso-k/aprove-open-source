package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.math.*;
import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * f(x,y): ax + by + cxy + d, f(x): ax^2 + bx + c.
 */
public class GInterpretationModeSimpleMixed<C extends GPolyCoeff>
        extends GInterpretationModeSimple<C> {

    @ParamsViaArguments("maxSimpleDegree")
    public GInterpretationModeSimpleMixed(int maxSimpleDegree) {
        super(maxSimpleDegree);
    }

    @Override
    public OrderPoly<C> getPolynomial(GInterpretation<C> interp,
            FunctionSymbol fs, List<OrderPoly<C>> variables) {
        int arity = fs.getArity();
        if (arity != 1) {
            return super.getPolynomial(interp, fs, variables);
        }

        OrderPoly<C> sum = this.getFreshVariableMonomial(interp, fs);

        OrderPoly<C> coefficient = this.getFreshVariableMonomial(interp, fs);
        sum = interp.factory.plus(sum,
                interp.factory.times(coefficient, variables.get(0)));

        coefficient = this.getFreshVariableMonomial(interp, fs);
        BigInteger two = BigInteger.valueOf(2);
        sum = interp.factory.plus(sum,
                interp.factory.times(coefficient,
                        interp.factory.power(variables.get(0), two)));
        return sum;
    }

}
