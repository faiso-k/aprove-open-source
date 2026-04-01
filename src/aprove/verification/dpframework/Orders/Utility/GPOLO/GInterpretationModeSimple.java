package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * ax + by + cxy + d.
 */
public class GInterpretationModeSimple<C extends GPolyCoeff> extends GInterpretationMode<C> {

    private final int maxSimpleDegree;

    @ParamsViaArguments("maxSimpleDegree")
    public GInterpretationModeSimple(int maxSimpleDegree) {
       this.maxSimpleDegree = maxSimpleDegree;
    }

    @Override
    public OrderPoly<C> getPolynomial(GInterpretation<C> interp,
            FunctionSymbol fs, List<OrderPoly<C>> variables) {
        int arity = fs.getArity();
        Set<GPolyVar> xs = new LinkedHashSet<GPolyVar>();
        for (int i = 0; i < arity; i++) {
            xs.add(interp.getVariableForFunctionSymbolArgument(i));
        }

        PowerSet<GPolyVar> variableSets;
        variableSets = new PowerSet<GPolyVar>(ImmutableCreator.create(xs),
                this.maxSimpleDegree, false);

        OrderPoly<C> sum = this.getZeroMonomial(interp);

        for (Set<GPolyVar> vars : variableSets) {
            // FIXME: getFreshVariableMonomial?
            GPoly<C, GPolyVar> factor = interp.getNextCoeffPoly(fs);

            // factor*xyz
            VarPartNode<GPolyVar> varsNode =
                interp.factory.buildVariables(vars);
            OrderPoly<C> addend = interp.factory.concat(factor, varsNode);
            sum = interp.factory.plus(sum, addend);
        }
        return sum;
    }

}
