/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Every factory implementing this interface must be able to create GPolys
 * of all kinds.
 * @author cotto
 * @version $Id$
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public interface GPolyFactory<C extends GPolyCoeff, V extends GPolyVar> extends Ring<GPoly<C, V>> {
    /**
     * @return the variable part node representing one.
     */
    VarPartNode<V> getVarOne();

    /**
     * @return the coeff representing one.
     */
    C getCoeffOne();

    /**
     * Create a variable.
     * @param var The variable.
     * @return A Node that represents the given variable.
     */
    VarPartNode<V> buildVariable(V var);

    /**
     * Create a GPoly 1*v from the given variable.
     * @param var The variable.
     * @return 1*v.
     */
    GPoly<C, V> buildFromVariable(V var);

    /**
     * Create a GPoly 1*(x*y*z*...) for the given variables.
     * @param vars The variables x,y,z,...
     * @return 1*(x*y*z*...).
     */
    VarPartNode<V> buildVariables(Collection<V> vars);

    /**
     * Create a GPoly c*1 from the given coefficient.
     * @param coeff The coefficient.
     * @return c*1.
     */
    GPoly<C, V> buildFromCoeff(C coeff);

    /**
     * Build the product of two variable parts, e.g. xy * x = x^2y.
     * @param one The first factor.
     * @param two The second factor.
     * @return A node that represents the product of the two parameters.
     */
    VarPartNode<V> times(VarPartNode<V> one, VarPartNode<V> two);

    /**
     * Create powers of the given VarPartNode.
     * @param base The VarPartNode that is the base.
     * @param exponent The exponent that should be applied.
     * @return A VarPartNode which is the old VarPartNode to the given power.
     */
    VarPartNode<V> power(VarPartNode<V> base, BigInteger exponent);

    /**
     * Concatenate a coefficient and a variable part to create a monomial.
     * @param coeff The coefficient.
     * @param varPart The variable part.
     * @return A node representing a monomial based on the coefficient and the
     * variable part.
     */
    GPoly<C, V> concat(C coeff, VarPartNode<V> varPart);

    /**
     * Add the two given polynomials.
     * @param one The first addend.
     * @param two The second addend.
     * @return A node representing the sum of the two given polynomials.
     */
    @Override
    GPoly<C, V> plus(GPoly<C, V> one, GPoly<C, V> two);

    /**
     * Add the given polynomials.
     * @param polys Some collection containing the polynomials to be added.
     * @return A node representing the sum of the given polynomials.
     */
    GPoly<C, V> plus(Collection<? extends GPoly<C, V>> polys);

    /**
     * Subtract the two given polynomials.
     * @param minuend The minuend.
     * @param subtrahend The subtrahend.
     * @return A node representing the difference minuend - subtrahend.
     */
    @Override
    GPoly<C, V> minus(GPoly<C, V> minuend, GPoly<C, V> subtrahend);

    /**
     * Multiply the two given polynomials, one*two.
     * @param one The first factor.
     * @param two The second factor.
     * @return A node representing the product of the two given polynomials.
     */
    @Override
    GPoly<C, V> times(GPoly<C, V> one, GPoly<C, V> two);

    /**
     * Get the minimum of the given polynomials.
     * @param polys Some collection containing the polynomials.
     * @return A node representing the minimum of the given polynomials.
     */
    GPoly<C, V> min(Collection<GPoly<C, V>> polys);

    /**
     * Get the minimum of the two given polynomials, min(one, two).
     * @param one The first polynomial.
     * @param two The second polynomial.
     * @return A node representing the minimum of the two given polynomials.
     */
    GPoly<C, V> min(GPoly<C, V> one, GPoly<C, V> two);

    /**
     * Get the maximum of the given polynomials.
     * @param polys Some collection containing the polynomials.
     * @return A node representing the maximum of the given polynomials.
     */
    GPoly<C, V> max(Collection<GPoly<C, V>> polys);

    /**
     * Get the maximum of the two given polynomials, max(one, two).
     * @param one The first polynomial.
     * @param two The second polynomial.
     * @return A node representing the maximum of the two given polynomials.
     */
    GPoly<C, V> max(GPoly<C, V> one, GPoly<C, V> two);

    /**
     * Calculate the power of base to the exponent.
     * @param base The base.
     * @param exponent The exponent.
     * @return A node representing the power base^exponent.
     */
    GPoly<C, V> power(GPoly<C, V> base, BigInteger exponent);

    /**
     * Replace every occurrence of the given variable in the map's key set by
     * the corresponding polynomial in the value set.
     * @param target The polynomial where the substution should take place.
     * @param replacement The variables and their corresponding substitution.
     * @param ringC A ring to operate on coefficients; use for advanced substitution of vars by constants.
     * @param aborter an aborter
     * @return a GPoly where all occurrences of the given variable are replaced
     * by the given polynomial.
     * @throws AbortionException when the aborter kicks in
     */
    GPoly<C, V> substituteVariables(GPoly<C, V> target,
        Map<V, ? extends GPoly<C, V>> replacement,
        Semiring<C> ringC,
        Abortion aborter) throws AbortionException;

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
    GPoly<C, V> substituteCoefficient(GPoly<C, V> target, C coeff, C substitute, Semiring<C> ringC);

    /**
     * Clear everything because this factory is not needed anymore.
     */
    void clear();
}
