/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This factory has a cache for every node ever created. Repeated operations
 * will always result in the very same ("==") result.
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public class FullSharingFactory<C extends GPolyCoeff, V extends GPolyVar> implements GPolyFactory<C, V> {
    /**
     * This variable part node always is interpreted as 1 in any monomial
     * monoid.
     */
    private final VarPartNode<V> varPartOne = new VarPartNode<>();

    /**
     * This coeff always is interpreted as 1 in any coeff ring.
     */
    private final C coeffOne = null;

    /**
     * Cache for variable part nodes holding a single variable.
     */
    private final Map<Collection<V>, VarPartNode<V>> varCache = new HashMap<>();

    /**
     * Cache for concatenations (monomials).
     */
    private final Map<Pair<C, VarPartNode<V>>, ConcatNode<C, V>> concatCache = new HashMap<>();

    /**
     * Cache for plus operations.
     */
    private final Map<Set<GPoly<C, V>>, GPoly<C, V>> plusCache = new HashMap<>();

    /**
     * Cache for minus operations.
     */
    private final Map<Pair<GPoly<C, V>, GPoly<C, V>>, GPoly<C, V>> minusCache = new HashMap<>();

    /**
     * Cache for times operations.
     */
    private final Map<Set<GPoly<C, V>>, GPoly<C, V>> timesCache = new HashMap<>();

    /**
     * Cache for times operations.
     */
    private final Map<Set<GPoly<C, V>>, GPoly<C, V>> minCache = new HashMap<>();

    /**
     * Cache for times operations.
     */
    private final Map<Set<GPoly<C, V>>, GPoly<C, V>> maxCache = new HashMap<>();

    /**
     * Cache for variable parts.
     */
    private final Map<Set<VarPartNode<V>>, VarPartNode<V>> varPartCache = new HashMap<>();

    /**
     * The polynomial representing 1.
     */
    private final GPoly<C, V> one = this.concat(this.coeffOne, this.varPartOne);

    /**
     * Create a variable part node holding a single variable.
     * @param var The variable defining the node.
     * @return A node representing the given variable.
     */
    @Override
    public VarPartNode<V> buildVariable(final V var) {
        VarPartNode<V> result = this.varCache.get(var);
        if (result == null) {
            result = new VarPartNode<>(var);
            this.varCache.put(Collections.singletonList(var), result);
        }
        return result;
    }

    /**
     * @return the variable part node representing 1 in any monomial monoid.
     */
    @Override
    public VarPartNode<V> getVarOne() {
        return this.varPartOne;
    }

    /**
     * @return the coeff representing 1 in any coeff ring.
     */
    @Override
    public C getCoeffOne() {
        return this.coeffOne;
    }

    /**
     * Create a node representing the concatenation of the coefficient and the
     * variable part.
     * @param coeff The coefficient.
     * @param varPart The variable part.
     * @return A node representing the concatenation of the coefficient and the
     * variable part.
     */
    @Override
    public GPoly<C, V> concat(final C coeff, final VarPartNode<V> varPart) {
        final Pair<C, VarPartNode<V>> pair = new Pair<>(coeff, varPart);
        ConcatNode<C, V> result = this.concatCache.get(pair);
        if (result == null) {
            result = new ConcatNode<>(coeff, varPart);
            this.concatCache.put(pair, result);
        }
        return result;
    }

    /**
     * Create a node representing the product of the two given variable part
     * nodes. Note that the order is not important, as an commutative monoid is
     * used to operate on variables.
     * @param oneParam The first factor.
     * @param twoParam The second factor.
     * @return A node representing the product of the two given variable part
     * nodes.
     */
    @Override
    public VarPartNode<V> times(final VarPartNode<V> oneParam, final VarPartNode<V> twoParam) {
        if (oneParam.isOne()) {
            return twoParam;
        }
        if (twoParam.isOne()) {
            return oneParam;
        }
        final Set<VarPartNode<V>> set = new LinkedHashSet<>(2);
        set.add(oneParam);
        set.add(twoParam);
        VarPartNode<V> result = this.varPartCache.get(set);
        if (result == null) {
            result = new VarPartNode<>(oneParam, twoParam);
            this.varPartCache.put(set, result);
        }
        return result;
    }

    /**
     * Add the two given polynomials.
     * @param oneParam The first addend.
     * @param twoParam The second addend.
     * @return A node representing the sum of the two given poly nodes.
     */
    @Override
    public GPoly<C, V> plus(final GPoly<C, V> oneParam, final GPoly<C, V> twoParam) {
        if (oneParam.isZero()) {
            return twoParam;
        }
        if (twoParam.isZero()) {
            return oneParam;
        }
        final Set<GPoly<C, V>> set = new LinkedHashSet<>(2);
        set.add(oneParam);
        set.add(twoParam);
        GPoly<C, V> result = this.plusCache.get(set);
        if (result == null) {
            result = new PlusNode<>(oneParam, twoParam);
            this.plusCache.put(set, result);
        }
        return result;
    }

    /**
     * Add the given polynomials.
     * @param polys Some collection containing the polynomials to be added.
     * @return A node representing the sum of the given polynomials.
     */
    @Override
    public GPoly<C, V> plus(final Collection<? extends GPoly<C, V>> polys) {
        if (polys.size() == 0) {
            return this.zero();
        } else if (polys.size() == 1) {
            return polys.iterator().next();
        } else {
            final Iterator<? extends GPoly<C, V>> it = polys.iterator();
            final GPoly<C, V> first = it.next();
            final GPoly<C, V> second = it.next();
            GPoly<C, V> sum = this.plus(first, second);
            while (it.hasNext()) {
                sum = this.plus(sum, it.next());
            }
            return sum;
        }
    }

    /**
     * Subtract the two given polynomials.
     * @param minuend The minuend.
     * @param subtrahend The subtrahend.
     * @return A node representing the difference minuend - subtrahend.
     */
    @Override
    public GPoly<C, V> minus(final GPoly<C, V> minuend, final GPoly<C, V> subtrahend) {
        if (minuend.equals(subtrahend) && !(minuend.isOne() && subtrahend.isOne())) {
            return this.zero();
        }
        if (subtrahend.isZero()) {
            return minuend;
        }
        final Pair<GPoly<C, V>, GPoly<C, V>> pair = new Pair<>(minuend, subtrahend);
        GPoly<C, V> result = this.minusCache.get(pair);
        if (result == null) {
            result = new MinusNode<>(minuend, subtrahend);
            this.minusCache.put(pair, result);
        }
        return result;
    }

    /**
     * Multiply the two given polynomials, one*two.
     * @param oneParam The first factor.
     * @param twoParam The second factor.
     * @return A node representing the product of the two given polynomial
     * nodes.
     */
    @Override
    public GPoly<C, V> times(final GPoly<C, V> oneParam, final GPoly<C, V> twoParam) {
        if (oneParam.isOne() || twoParam.isZero()) {
            return twoParam;
        }
        if (twoParam.isOne() || oneParam.isZero()) {
            return oneParam;
        }
        final Set<GPoly<C, V>> set = new LinkedHashSet<>(2);
        set.add(oneParam);
        set.add(twoParam);
        GPoly<C, V> result = this.timesCache.get(set);
        if (result == null) {
            result = new TimesNode<>(oneParam, twoParam);
            this.timesCache.put(set, result);
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public GPoly<C, V> min(final GPoly<C, V> oneParam, final GPoly<C, V> twoParam) {
        final Set<GPoly<C, V>> set = new LinkedHashSet<>(2);
        set.add(oneParam);
        set.add(twoParam);
        GPoly<C, V> result = this.minCache.get(set);
        if (result == null) {
            result = new MinNode<>(oneParam, twoParam);
            this.minCache.put(set, result);
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public GPoly<C, V> min(final Collection<GPoly<C, V>> polys) {
        if (polys.size() == 0) {
            return this.zero();
        } else if (polys.size() == 1) {
            return polys.iterator().next();
        } else {
            final Iterator<GPoly<C, V>> it = polys.iterator();
            final GPoly<C, V> first = it.next();
            final GPoly<C, V> second = it.next();
            GPoly<C, V> min = this.min(first, second);
            while (it.hasNext()) {
                min = this.min(min, it.next());
            }
            return min;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public GPoly<C, V> max(final GPoly<C, V> oneParam, final GPoly<C, V> twoParam) {
        final Set<GPoly<C, V>> set = new LinkedHashSet<>(2);
        set.add(oneParam);
        set.add(twoParam);
        GPoly<C, V> result = this.maxCache.get(set);
        if (result == null) {
            result = new MaxNode<>(oneParam, twoParam);
            this.maxCache.put(set, result);
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public GPoly<C, V> max(final Collection<GPoly<C, V>> polys) {
        if (polys.size() == 0) {
            return this.zero();
        } else if (polys.size() == 1) {
            return polys.iterator().next();
        } else {
            final Iterator<GPoly<C, V>> it = polys.iterator();
            final GPoly<C, V> first = it.next();
            final GPoly<C, V> second = it.next();
            GPoly<C, V> max = this.max(first, second);
            while (it.hasNext()) {
                max = this.max(max, it.next());
            }
            return max;
        }
    }

    /**
     * Create a polynomial node that is base^exponent.
     * @param base The base, which is a polynomial node.
     * @param exponent The exponent.
     * @return A node that is base^exponent.
     */
    @Override
    public GPoly<C, V> power(final GPoly<C, V> base, final BigInteger exponent) {
        if (exponent.signum() < 0) {
            if (Globals.useAssertions) {
                assert (false) : "Please implement dealing with negative exponents!";
            }
            return null;
        }
        if (exponent.equals(BigInteger.ZERO)) {
            return this.one;
        } else if (exponent.equals(BigInteger.ONE)) {
            return base;
        } else {
            final BigInteger two = BigInteger.valueOf(2);
            GPoly<C, V> result = this.one;
            GPoly<C, V> tmp = base;
            BigInteger exp = exponent;
            while (exp.signum() > 0) {
                if (exp.mod(two).equals(BigInteger.ONE)) {
                    result = this.times(result, tmp);
                }
                exp = exp.divide(two);
                if (exp.signum() > 0) {
                    tmp = this.times(tmp, tmp);
                } else {
                    break;
                    // somewhat ugly, but slightly more efficient
                    // (saves the last check of the loop cond.)
                }
            }
            return result;
        }
    }

    /**
     * Create a variable part node that is base^exponent.
     * @param base The base, which is a variable part node.
     * @param exponent The exponent.
     * @return A variable part node that is base^exponent.
     */
    @Override
    public VarPartNode<V> power(final VarPartNode<V> base, final BigInteger exponent) {
        if (exponent.signum() < 0) {
            if (Globals.useAssertions) {
                assert (false) : "Please implement dealing with negative exponents!";
            }
        }
        if (exponent.equals(BigInteger.ZERO)) {
            return this.varPartOne;
        } else if (exponent.equals(BigInteger.ONE)) {
            return base;
        } else {
            final BigInteger two = BigInteger.valueOf(2);
            VarPartNode<V> result = this.varPartOne;
            VarPartNode<V> tmp = base;
            BigInteger exp = exponent;
            while (exp.signum() > 0) {
                if (exp.mod(two).equals(BigInteger.ONE)) {
                    result = this.times(result, tmp);
                }
                exp = exp.divide(two);
                if (exp.signum() > 0) {
                    tmp = this.times(tmp, tmp);
                } else {
                    break;
                    // somewhat ugly, but slightly more efficient
                    // (saves the last check of the loop cond.)
                }
            }
            return result;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public GPoly<C, V> substituteVariables(final GPoly<C, V> target,
        final Map<V, ? extends GPoly<C, V>> replacement,
        final Semiring<C> ringC,
        final Abortion aborter) throws AbortionException {
        final VarSubstitutionVisitor<C, V> vsv = new VarSubstitutionVisitor<>(replacement, this, ringC);
        aborter.checkAbortion();
        return vsv.applyTo(target);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public GPoly<C, V> substituteCoefficient(final GPoly<C, V> target,
        final C coeff,
        final C substitute,
        final Semiring<C> ringC) {
        if (Globals.useAssertions) {
            assert (!coeff.equals(substitute));
        }
        final CoeffSubstitutionVisitor<C, V> csv = new CoeffSubstitutionVisitor<>(coeff, substitute, this, ringC);
        return csv.applyTo(target);
    }

    /**
     * Create a GPoly 1*v from the given variable.
     * @param var The variable.
     * @return 1*v.
     */
    @Override
    public GPoly<C, V> buildFromVariable(final V var) {
        final VarPartNode<V> varPartNode = this.buildVariable(var);
        return this.concat(this.coeffOne, varPartNode);
    }

    /**
     * Create a GPoly c*1 from the given coefficient.
     * @param coeff The coefficient.
     * @return c*1.
     */
    @Override
    public GPoly<C, V> buildFromCoeff(final C coeff) {
        return this.concat(coeff, this.varPartOne);
    }

    /**
     * Create a GPoly 1*(x*y*z*...) for the given variables.
     * @param vars The variables x,y,z,...
     * @return 1*(x*y*z*...).
     */
    @Override
    public VarPartNode<V> buildVariables(final Collection<V> vars) {
        VarPartNode<V> result = this.varCache.get(vars);
        if (result == null) {
            result = new VarPartNode<>(vars);
            this.varCache.put(vars, result);
        }
        return result;
    }

    /**
     * @return the inverse element of the given polynomial.
     * @param target Get the inverse of this.
     */
    @Override
    public GPoly<C, V> getInverse(final GPoly<C, V> target) {
        return this.minus(this.zero(), target);
    }

    /**
     * @return the GPoly representing 1.
     */
    @Override
    public GPoly<C, V> one() {
        return this.one;
    }

    /**
     * @return the GPoly representing 0.
     */
    @Override
    public GPoly<C, V> zero() {
        // is there a better representation?
        return this.minus(this.one(), this.one());
    }

    /**
     * Clear all caches.
     */
    @Override
    public void clear() {
        this.concatCache.clear();
        this.minusCache.clear();
        this.plusCache.clear();
        this.timesCache.clear();
        this.varCache.clear();
        this.varPartCache.clear();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isRing() {
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public SpecializedGInterpretation getSpecializedGInterpretation() {
        return DummySpecializedGInterpretation.create();
    }

}
