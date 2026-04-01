package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Polynomial of order <code>degree</code>
 */
public class GInterpretationModeDegree<C extends GPolyCoeff> extends GInterpretationMode<C> {

    private final int degree;

    @ParamsViaArguments("degree")
    public GInterpretationModeDegree(int degree) {
        this.degree = degree;
    }

    @Override
    public OrderPoly<C> getPolynomial(GInterpretation<C> interp,
            FunctionSymbol fs, List<OrderPoly<C>> variables) {
        Set<OrderPoly<C>> xs = new LinkedHashSet<OrderPoly<C>>(variables);
        OrderPoly<C> sum = this.getZeroMonomial(interp);
        for (MultiSet<OrderPoly<C>> someXs
                : PowerMultiSet.createDestructively(xs, this.degree, false)) {
            OrderPoly<C> prod = this.getFreshVariableMonomial(interp, fs);

            for (Entry<OrderPoly<C>, Integer> x : someXs.entrySet()) {
                // Carsten Fuhs said it is OK to use integers here.
                OrderPoly<C> xPow =
                    interp.factory.power(
                            x.getKey(), BigInteger.valueOf(x.getValue()));
                prod = interp.factory.times(prod, xPow);
            }
            sum = interp.factory.plus(sum, prod);
        }
        return sum;
    }

}
