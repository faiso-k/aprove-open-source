/**
 * @author cotto
 * @version $Id$
 */

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
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A standard implementation of the ring over integers we know from
 * kindergarten.
 * @author cotto
 */
public class BigIntImmutableRing extends Ring.RingSkeleton<BigIntImmutable> {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.BigIntImmutableRing");

    private static final MySGInterp specializedInterp =
        new MySGInterp();

    /**
     * @return 0.
     */
    @Override
    public BigIntImmutable zero() {
        return this.wrap(BigInteger.ZERO);
    }

    /**
     * @return 1.
     */
    @Override
    public BigIntImmutable one() {
        return this.wrap(BigInteger.ONE);
    }

    /**
     * @param first first addend.
     * @param second second addend.
     * @return first+second.
     */
    @Override
    public BigIntImmutable plus(
            final BigIntImmutable first,
            final BigIntImmutable second) {
        return this.wrap(first.getBigInt().add(second.getBigInt()));
    }

    /**
     * @param first first factor.
     * @param second second factor.
     * @return first*second.
     */
    @Override
    public BigIntImmutable times(
            final BigIntImmutable first,
            final BigIntImmutable second) {
        return this.wrap(first.getBigInt().multiply(second.getBigInt()));
    }

    /**
     * @param minuend Minuend.
     * @param subtrahend Subtrahend.
     * @return minuend - subtrahend.
     */
    @Override
    public BigIntImmutable minus(
            final BigIntImmutable minuend,
            final BigIntImmutable subtrahend) {
        return this.wrap(minuend.getBigInt().subtract(subtrahend.getBigInt()));
    }

    /**
     * @param target We want -target.
     * @return -target.
     */
    @Override
    public BigIntImmutable getInverse(final BigIntImmutable target) {
        return this.wrap(BigInteger.ZERO.subtract(target.getBigInt()));
    }

    /**
     * Get the BigIntImmutable for the given BigInteger.
     * @param bigInt The BigInteger.
     * @return Some BigIntImmutable for the given BigInteger.
     */
    private BigIntImmutable wrap(final BigInteger bigInt) {
        return BigIntImmutable.create(bigInt);
    }

    @Override
    public SpecializedGInterpretation getSpecializedGInterpretation() {
        return BigIntImmutableRing.specializedInterp;

    }

    /**
     * Computes conditional strong monotonicity constraints for each argument of
     * the FunctionSymbol fs w.r.t. to the interpretation interp.
     *
     * For each argument, a variable is returned. If this variable is set to
     * one, the monotonicity constraint is enabled; if set to zero, it is
     * disabled.
     *
     * @param constraints
     *            Stores the generated constraints
     * @param boolRange
     *            Range for boolean variables (i.e. 0 or 1)
     */
    public static List<OrderPoly<BigIntImmutable>> getStrongMonotonicityConstraints(
            GInterpretation<BigIntImmutable> interp, FunctionSymbol fs,
            Set<OrderPolyConstraint<BigIntImmutable>> constraints,
            OPCRange<BigIntImmutable> boolRange) {
        return BigIntImmutableRing.specializedInterp.getStrongMonotonicityConstraints(
                interp, fs, constraints, boolRange);
    }

    private static class MySGInterp implements SpecializedGInterpretation {

        public <C extends GPolyCoeff> List<OrderPoly<C>> getStrongMonotonicityConstraints(
                GInterpretation<C> interp, FunctionSymbol fs,
                Set<OrderPolyConstraint<C>> constraints,
                OPCRange<C> boolRange) {
            OrderPolyFactory<C> opcFactory = interp.getFactory();
            OrderPoly<C> zero = opcFactory.getZero();

            OrderPoly<C> poly = interp.getPol().get(fs);
            Map<GPolyVar, Collection<GPoly<C, GPolyVar>>> coeffsPerVar =
                this.getRelevantCoeffsPerVar(interp, poly);
            int arity = fs.getArity();
            List<OrderPoly<C>> result =
                new ArrayList<OrderPoly<C>>(arity);
            for (int i=0; i < arity; i++) {
                Collection<GPoly<C, GPolyVar>> coeffs =
                    coeffsPerVar.get(interp.getVariableForFunctionSymbolArgument(i));

                GPolyVar monVar = interp.getNextCoeff(
                            "mc." + fs.getName() + "." + fs.getArity() + "." + i + "_", boolRange);
                interp.getRanges().put(monVar, boolRange);
                OrderPoly<C> monVarPoly = opcFactory.buildFromInnerVariable(monVar);
                result.add(monVarPoly);
                if (coeffs == null || coeffs.isEmpty()) {
                    OrderPoly<C> constraintPoly = opcFactory.times(
                            monVarPoly,
                            opcFactory.minus(opcFactory.getZero(), opcFactory.getOne()));
                    constraints.add(
                            interp.getConstraintFactory().createWithQuantifier(
                                    constraintPoly, ConstraintType.GE));
                } else {
                    OrderPoly<C> newPoly = zero;
                    for (GPoly<C, GPolyVar> coeff : coeffs) {
                        newPoly = opcFactory.plus(newPoly, opcFactory.buildFromCoeff(coeff));
                    }
                    newPoly = opcFactory.plus(
                            newPoly,
                            opcFactory.minus(opcFactory.getOne(), monVarPoly));
                    OrderPolyConstraint<C> opc =
                        interp.getConstraintFactory().createWithQuantifier(
                                newPoly, ConstraintType.GT);
                    constraints.add(opc);
                }
            }
            return result;
        }

        /**
         * For each function symbol f(x_1, ..., x_n) with some interpretation pol the constraints
         * a_(i,1) + ... + a_(i,n_i) > 0 will be created where the a_(i,j) are all coefficients
         * of monomials which only have x_i as variables.
         *
         * @return poly constraints which ensure strong monotonicity of the {@link GInterpretation}.
         */
        @Override
        public <C extends GPolyCoeff> Set<OrderPolyConstraint<C>> getStrongMonotonicityConstraints(
                GInterpretation<C> interp) {
            Set<OrderPolyConstraint<C>> constraints =
                new LinkedHashSet<OrderPolyConstraint<C>>();
            OrderPolyFactory<C> opcFactory = interp.getFactory();
            OrderPoly<C> zero = opcFactory.getZero();
            for (Map.Entry<FunctionSymbol, OrderPoly<C>> entry : interp.getPol().entrySet()) {
                OrderPoly<C> poly = entry.getValue();
                Map<GPolyVar, Collection<GPoly<C, GPolyVar>>> coeffsPerVar =
                    this.getRelevantCoeffsPerVar(interp, poly);
                if (coeffsPerVar.keySet().size() < entry.getKey().getArity()) {
                    /*
                     * There is at least one parameter of the function symbol,
                     * which has no pendant in the corresponding polynomial
                     * interpretation. Therefore, strong monotonicity is
                     * not possible and we return an unsatisfiable constraint.
                     */
                    BigIntImmutableRing.log.warning("Strong monotonicity requires the polynomial" +
                            " interpretation to contain all parameters. This" +
                            " is not the case for " + entry.getKey() +
                            " with interpretation " + poly);
                    return Collections.singleton(
                            interp.getConstraintFactory().createFalse());

                }
                for (Collection<GPoly<C, GPolyVar>> coeffs : coeffsPerVar.values()) {
                    OrderPoly<C> newPoly = zero;
                    for (GPoly<C, GPolyVar> coeff : coeffs) {
                        newPoly = opcFactory.plus(newPoly, opcFactory.buildFromCoeff(coeff));
                    }
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
         * x_n^k_(i,n) create a map x_j -&gt; {a_(j,1), ... a_(j,n_j)} where the
         * a_(j,i) are the coefficients of the monomials which have k_(i,j) != 0
         * and k_(i,j') = 0 for all j != j'.
         *
         * See getStrongMonotonicityConstraints above.
         */
        private <C extends GPolyCoeff> Map<GPolyVar, Collection<GPoly<C, GPolyVar>>> getRelevantCoeffsPerVar(
                GInterpretation<C> interp, OrderPoly<C> poly) {
            if (!poly.isFlat(interp.getOuterRingMonoid())) {
                poly.deepFlatten(interp.getFvInner(), interp.getFvOuter());
            }
            ImmutableMap<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monomials =
                poly.getMonomials(interp.getOuterRingMonoid());
            CollectionMap<GPolyVar, GPoly<C, GPolyVar>> coeffsPerVar =
                new CollectionMap<GPolyVar, GPoly<C, GPolyVar>>(CollectionCreator.arrayList());
            for (Map.Entry<GMonomial<GPolyVar>,GPoly<C, GPolyVar>> entry : monomials.entrySet()) {
                GMonomial<GPolyVar> varpart = entry.getKey();
                GPoly<C, GPolyVar> coeff = entry.getValue();

                GPolyVar var = null;
                for (Map.Entry<GPolyVar, BigInteger> expEntry : varpart.getExponents().entrySet()) {
                    if (expEntry.getValue().signum() != 0) {
                        if (var == null) {
                            var = expEntry.getKey();
                        } else {
                            var = null;
                            break;
                        }
                    }
                }
                if (var != null) {
                    coeffsPerVar.add(var, coeff);
                }
            }
            return coeffsPerVar;
        }

        @Override
        public <C extends GPolyCoeff> boolean isStronglyMonotonic(
                GInterpretation<C> interp,
                OrderPoly<C> poly, GPolyVar var) {
            if (!poly.isFlat(interp.getOuterRingMonoid())) {
                poly.deepFlatten(interp.getFvInner(), interp.getFvOuter());
            }
            ImmutableMap<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monomials =
                poly.getMonomials(interp.getOuterRingMonoid());
            ArrayList<BigIntImmutable> relevantCoeffs =
                new ArrayList<BigIntImmutable>();
            outer : for (Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> entry : monomials.entrySet()) {
                GMonomial<GPolyVar> varpart = entry.getKey();
                GPoly<C, GPolyVar> coeff = entry.getValue();


                for (Map.Entry<GPolyVar, BigInteger> expEntry : varpart.getExponents().entrySet()) {
                    if (var.equals(expEntry.getKey())) {
                        if (expEntry.getValue().equals(BigInteger.ZERO)) {
                            continue outer;
                        } else {
                            assert(coeff.getVariables().size() == 0);
                            assert(coeff.getCoeffs().size() == 1);
                            C coeffVal = coeff.getCoeffs().get(0);
                            assert(coeffVal instanceof BigIntImmutable);
                            relevantCoeffs.add((BigIntImmutable) coeffVal);
                        }
                    } else if (!expEntry.getValue().equals(BigInteger.ZERO)) {
                        continue outer;
                    }
                }
            }

            boolean posCoeffFound = false;
            for(BigIntImmutable rc : relevantCoeffs) {
                switch (rc.getBigInt().signum()) {
                    case 1:
                        posCoeffFound = true;
                        break;
                    case -1:
                        return false;
                }
            }
            return posCoeffFound;
        }

    }

}
