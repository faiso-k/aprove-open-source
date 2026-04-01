package aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public abstract class SubsetOfQRing<T> extends Ring.RingSkeleton<T> {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.SubsetOfQRing");

    private static final SpecializedGInterpretation specializedInterp =
        new MySGInterp();

    @Override
    public SpecializedGInterpretation getSpecializedGInterpretation() {
        return SubsetOfQRing.specializedInterp;
    }

    private static class MySGInterp implements SpecializedGInterpretation {

        /**
         * For each function symbol f(x_1, ..., x_n) with some interpretation pol the constraints
         * a_i >= 1 will be created where the a_i is the coefficient of the
         * monomial a_i*x_i.
         *
         * @return polynomial constraints which ensure strong monotonicity of the {@link GInterpretation}.
         */
        @Override
        public <C extends GPolyCoeff> Set<OrderPolyConstraint<C>> getStrongMonotonicityConstraints(
                GInterpretation<C> interp) {
            Set<OrderPolyConstraint<C>> constraints =
                new LinkedHashSet<OrderPolyConstraint<C>>();
            OrderPolyFactory<C> opcFactory = interp.getFactory();
            OrderPoly<C> one = opcFactory.getOne();
            for (Map.Entry<FunctionSymbol, OrderPoly<C>> entry : interp.getPol().entrySet()) {
                OrderPoly<C> poly = entry.getValue();
                Map<GPolyVar, GPoly<C, GPolyVar>> coeffPerVar =
                    this.getRelevantCoeffPerVar(interp, poly);
                if (coeffPerVar.keySet().size() < entry.getKey().getArity()) {
                    /*
                     * There is at least one parameter of the function symbol,
                     * which has no pendant in the corresponding polynomial
                     * interpretation. Therefore, strong monotonicity is
                     * not possible and we return an unsatisfiable constraint.
                     */
                    SubsetOfQRing.log.warning("Strong monotonicity requires the polynomial" +
                            " interpretation to contain all parameters. This" +
                            " is not the case for " + entry.getKey() +
                            " with interpretation " + poly);
                    return Collections.singleton(
                            interp.getConstraintFactory().createFalse());

                }
                for (GPoly<C, GPolyVar> coeff : coeffPerVar.values()) {
                    OrderPoly<C> newPoly =
                        opcFactory.minus(opcFactory.buildFromCoeff(coeff), one);
                    OrderPolyConstraint<C> opc =
                        interp.getConstraintFactory().createWithQuantifier(
                                newPoly, ConstraintType.GT);
                    constraints.add(opc);
                }
            }
            return constraints;
        }

        /**
         * For an polynomial of the form \sum_i b_i * x_1^k_(i,1) * ... *
         * x_n^k_(i,n) create a map x_j -&gt; a_j where the
         * a_j is the coefficient of the monomial a_j * x_j.
         *
         * See getStrongMonotonicityConstraints above.
         */
        private <C extends GPolyCoeff> Map<GPolyVar, GPoly<C, GPolyVar>> getRelevantCoeffPerVar(
                GInterpretation<C> interp, OrderPoly<C> poly) {
            if (!poly.isFlat(interp.getOuterRingMonoid())) {
                poly.deepFlatten(interp.getFvInner(), interp.getFvOuter());
            }
            ImmutableMap<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monomials =
                poly.getMonomials(interp.getOuterRingMonoid());
            Map<GPolyVar, GPoly<C, GPolyVar>> coeffPerVar =
                new LinkedHashMap<GPolyVar, GPoly<C, GPolyVar>>();
            for (Map.Entry<GMonomial<GPolyVar>,GPoly<C, GPolyVar>> entry : monomials.entrySet()) {
                GMonomial<GPolyVar> varpart = entry.getKey();
                GPoly<C, GPolyVar> coeff = entry.getValue();

                for (Map.Entry<GPolyVar, BigInteger> expEntry : varpart.getExponents().entrySet()) {
                    if (expEntry.getValue().equals(BigInteger.ONE)) {
                        coeffPerVar.put(expEntry.getKey(), coeff);
                    }
                }
            }
            return coeffPerVar;
        }

        @Override
        public <C extends GPolyCoeff> boolean isStronglyMonotonic(
                GInterpretation<C> interp, OrderPoly<C> poly, GPolyVar var) {
            throw new UnsupportedOperationException();
        }

    }
}
