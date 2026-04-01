/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * This is just a wrapper that returns some OrderPoly<C> instead of the
 * equivalent GPoly&lt;GPoly&lt;C, Variable&gt;, Variable&gt;.
 * @param <C> The type of the coefficients.
 * @author cotto
 *
 */
public class OrderPolyFactory<C extends GPolyCoeff> {
    /**
     * This is the real factory creating polys.
     */
    private final GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> factory;

    /**
     * This factory is used to create coefficients for the outer polynomial.
     */
    private final GPolyFactory<C, GPolyVar> innerFactory;

    /**
     * Remember what OrderPoly already exists for the given GPoly.
     */
    private final Map<GPoly<GPoly<C, GPolyVar>, GPolyVar>, OrderPoly<C>> cache;

    /**
     * Create this wrapper based on the given factory.
     * @param polyFactory This is the real factory creating polynomials.
     * @param innerFactoryParam This factory will be used to create coefficients
     * for the outer polynomials.
     */
    public OrderPolyFactory(final GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> polyFactory,
            final GPolyFactory<C, GPolyVar> innerFactoryParam) {
        this.factory = polyFactory;
        this.innerFactory = innerFactoryParam;
        this.cache = new LinkedHashMap<GPoly<GPoly<C, GPolyVar>, GPolyVar>, OrderPoly<C>>();
    }

    /**
     * Wraps a GPoly into an equivalent OrderPoly
     *
     * @return the OrderPoly that corresponds to the given GPoly.
     * @param gpoly The GPoly that defines the OrderPoly.
     */
    public OrderPoly<C> wrap(final GPoly<GPoly<C, GPolyVar>, GPolyVar> gpoly) {
        OrderPoly<C> result = this.cache.get(gpoly);
        if (result == null) {
            result = new OrderPoly<C>(gpoly);
            this.cache.put(gpoly, result);
        }
        return result;
    }

    /**
     * Call factory.minus.
     * @param one First parameter.
     * @param two Second parameter.
     * @return Defined by factory.minus.
     */
    public OrderPoly<C> minus(final OrderPoly<C> one, final OrderPoly<C> two) {
        return this.wrap(this.factory.minus(one, two));
    }

    /**
     * Call factory.plus.
     * @param one First parameter.
     * @param two Second parameter.
     * @return Defined by factory.plus.
     */
    public OrderPoly<C> plus(final OrderPoly<C> one, final OrderPoly<C> two) {
        return this.wrap(this.factory.plus(one, two));
    }

    /**
     * Call factory.plus
     *
     * @param a
     *            collection of polys
     * @return Defined by factor plus
     */
    public OrderPoly<C> plus(final Collection<OrderPoly<C>> polys) {
        return this.wrap(this.factory.plus(polys));
    }

    /**
     * Call factory.times.
     * @param one First parameter.
     * @param two Second parameter.
     * @return Defined by factory.times.
     */
    public OrderPoly<C> times(final OrderPoly<C> one, final OrderPoly<C> two) {
        return this.wrap(this.factory.times(one, two));
    }

    /**
     * Create a poly 1*v based on the given variable.
     * @param var The variable.
     * @return 1*v.
     */
    public OrderPoly<C> buildFromVariable(final GPolyVar var) {
        return this.wrap(this.factory.buildFromVariable(var));
    }

    /**
     * @return a poly c*1 based on the given coefficient (which is a
     * GPoly&lt;C, Variable&gt;).
     * @param coeff The coefficient.
     */
    public OrderPoly<C> buildFromCoeff(final GPoly<C, GPolyVar> coeff) {
        return this.wrap(this.factory.concat(coeff, this.factory.getVarOne()));
    }

    /**
     * @param coeff The coefficient.
     * @return a poly c*1 based on the given coefficient (which is a C).
     */
    public OrderPoly<C> buildFromInnerCoeff(final C coeff) {
        final GPoly<C, GPolyVar> innerPoly = this.innerFactory.buildFromCoeff(coeff);
        return this.buildFromCoeff(innerPoly);
    }

    /**
     * @return factory.coeffOne
     */
    public GPoly<C, GPolyVar> getCoeffOne() {
        return this.factory.getCoeffOne();
    }

    /**
     * @return factory.buildVariable.
     * @param var The variable.
     */
    public VarPartNode<GPolyVar> buildVariable(final GPolyVar var) {
        return this.factory.buildVariable(var);
    }

    /**
     * @return factory.concat.
     * @param coeff The coefficient.
     * @param varPart The variable part node.
     */
    public OrderPoly<C> concat(final GPoly<C, GPolyVar> coeff, final VarPartNode<GPolyVar> varPart) {
        return this.wrap(this.factory.concat(coeff, varPart));
    }

    /**
     * Replace every occurrence of the given variable in the map's key set by
     * the corresponding polynomial in the value set.
     * @param target The polynomial where the substution should take place.
     * @param replacement The variables and their corresponding substitution.
     * @param ringC A ring to operate on (inner) coefficients; use for advanced
     * substitution of inner vars by constants.
     * @param aborter an aborter
     * @return a GPoly where all occurrences of the given variable are replaced
     * by the given polynomial.
     * @throws AbortionException when the aborter kicks in
     */
    public OrderPoly<C> substituteVariables(final OrderPoly<C> target,
        final Map<GPolyVar, GPoly<GPoly<C, GPolyVar>, GPolyVar>> replacement,
        final Semiring<GPoly<C, GPolyVar>> ringC,
        final Abortion aborter) throws AbortionException {
        return this.wrap(this.factory.substituteVariables(target, replacement, ringC, aborter));
    }

    /**
     * @return factory.getVarOne.
     */
    public VarPartNode<GPolyVar> getVarOne() {
        return this.factory.getVarOne();
    }

    public OrderPoly<C> getOne() {
        return this.wrap(this.factory.buildFromCoeff(this.getCoeffOne()));
    }

    public OrderPoly<C> getZero() {
        final OrderPoly<C> one = this.getOne();
        return this.minus(one, one);
    }

    /**
     * @return a poly (1*v)*1 where (1*v) is a coefficient of the outer
     * polynomial.
     * @param var The variable.
     */
    public OrderPoly<C> buildFromInnerVariable(final GPolyVar var) {
        final GPoly<C, GPolyVar> coeff = this.innerFactory.buildFromVariable(var);
        return this.buildFromCoeff(coeff);
    }

    /**
     * Allow direct access to the factory used to create the outer
     * polynomials.
     * @return the outer factory
     */
    public GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> getFactory() {
        return this.factory;
    }

    /**
     * Allow direct access to the inner factory used to create coefficients for
     * OrderPolys.
     * @return the inner factory.
     */
    public GPolyFactory<C, GPolyVar> getInnerFactory() {
        return this.innerFactory;
    }

    /**
     * Replace every occurrence of the given coefficient in the target by the
     * given new coefficient.
     * @param target The polynomial where the substution should take place.
     * @param coeff The coefficient to be replaced.
     * @param ringC A ring to operate on coefficients; use for advanced substitution of vars by constants.
     * @param substitute The coeff that should take the coeff's place.
     * @return a GPoly where all occurrences of the given coeff are replaced
     * by the given substitute.
     */
    public OrderPoly<C> substituteCoefficient(final OrderPoly<C> target,
        final GPoly<C, GPolyVar> coeff,
        final GPoly<C, GPolyVar> substitute,
        final Semiring<GPoly<C, GPolyVar>> ringC) {
        return this.wrap(this.factory.substituteCoefficient(target, coeff, substitute, ringC));
    }

    /**
     * Create a GPoly 1*(x*y*z*...) for the given variables.
     *
     * @param vars The variables.
     * @return factory.buildFromVariables.
     */
    public VarPartNode<GPolyVar> buildVariables(final Collection<GPolyVar> vars) {
        return this.factory.buildVariables(vars);
    }

    /**
     * @param base The base.
     * @param exp The exponent.
     * @return factory.power.
     */
    public OrderPoly<C> power(final OrderPoly<C> base, final BigInteger exp) {
        return this.wrap(this.factory.power(base, exp));
    }
}
