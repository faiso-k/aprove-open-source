/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.MaxMinToVarVisitor.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

public class GPolySimplifyer {

    public static <C extends GPolyCoeff> GPoly<GPoly<C, GPolyVar>, GPolyVar> simplify(GPoly<GPoly<C, GPolyVar>, GPolyVar> poly, final FlatteningVisitor <C, GPolyVar> fvInner,
                final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter,
                final GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> factory) {
        MaxMinToVarVisitor<C> visitor = new MaxMinToVarVisitor<C>(fvInner, fvOuter, factory);
        GPoly<GPoly<C, GPolyVar>, GPolyVar> withoutMax = visitor.applyTo(poly);
        if (withoutMax == poly) {
            return withoutMax;
        }
        if (!withoutMax.isFlat(fvOuter.getRingC(), fvOuter.getMonoid())) {
            fvOuter.applyTo(withoutMax);
        }
        return GPolySimplifyer.unfoldMaxVars(withoutMax, fvInner, fvOuter, factory);
    }


    protected static <C extends GPolyCoeff> GPoly<GPoly<C, GPolyVar>, GPolyVar> unfoldMaxVars(final GPoly<GPoly<C, GPolyVar>, GPolyVar> withoutMax,
            final FlatteningVisitor <C, GPolyVar> fvInner,
            final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter,
            final GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> factory) {
        GPoly<GPoly<C, GPolyVar>, GPolyVar> sum = null;
        for (Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monomial : withoutMax.getMonomials(fvOuter.getRingC(), fvOuter.getMonoid()).entrySet()) {
            List<GPolyVar> vars = new ArrayList<GPolyVar>();
            GPoly<GPoly<C, GPolyVar>, GPolyVar> maxPart = null;
            for (Map.Entry<GPolyVar, BigInteger> exp : monomial.getKey().getExponents().entrySet()) {
                if (exp.getKey() instanceof MaxMinToVarVisitor.MaxVar) {
                    MaxVar<C> max = (MaxVar<C>) exp.getKey();
                    GPoly<GPoly<C, GPolyVar>, GPolyVar> maxAdd = factory.max(GPolySimplifyer.unfoldMaxVars(max.left, fvInner, fvOuter, factory), GPolySimplifyer.unfoldMaxVars(max.right, fvInner, fvOuter, factory));
                    if (exp.getValue().compareTo(BigInteger.ONE) > 0) {
                        maxAdd = factory.power(maxAdd, exp.getValue());
                    }
                    if (maxPart == null) {
                        maxPart = maxAdd;
                    } else {
                        maxPart = factory.times(maxPart, maxAdd);
                    }
                } else if (exp.getKey() instanceof MaxMinToVarVisitor.MinVar) {
                    MinVar<C> min = (MinVar<C>) exp.getKey();
                    GPoly<GPoly<C, GPolyVar>, GPolyVar> minAdd = factory.min(GPolySimplifyer.unfoldMaxVars(min.left, fvInner, fvOuter, factory), GPolySimplifyer.unfoldMaxVars(min.right, fvInner, fvOuter, factory));
                    if (exp.getValue().compareTo(BigInteger.ONE) > 0) {
                        minAdd = factory.power(minAdd, exp.getValue());
                    }
                    if (maxPart == null) {
                        maxPart = minAdd;
                    } else {
                        maxPart = factory.times(maxPart, minAdd);
                    }
                } else {
                    for (int i = exp.getValue().intValue()-1; i>=0; i--) {
                        vars.add(exp.getKey());
                    }
                }
            }
            if (maxPart == null) {
                maxPart = factory.concat(monomial.getValue(), factory.buildVariables(vars));
            } else {
                maxPart = factory.times(maxPart,factory.concat(monomial.getValue(), factory.buildVariables(vars)));
            }
            if (sum == null) {
                sum = maxPart;
            } else {
                sum = factory.plus(sum, maxPart);
            }
        }
        return sum;
    }

}
