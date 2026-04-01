/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings;

import java.util.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import immutables.*;

/**
 * This class provides (semi-)ring operations on flat representations of Polynomials
 * using coefficients of type C and variables of type V. Whether its instances
 * represent actual rings or not depends on the type of the coefficient ring
 * plugged into them.
 *
 * For efficiency one might chose a factory as Ring over C which does not
 * actually compute the result (but represents the result using a DAG, which is
 * the way a GPoly works).
 * @author cotto
 * @version $Id$
 *
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public class SimpleGPolyFlatRing<C, V extends GPolyVar> implements GPolyFlatRing<C, V> {

    /**
     * A ring that can operate on coefficients of type C.
     */
    protected Semiring<C> rc;

    /**
     * A monoid that can operate on monomials of type GMonomial using V.
     */
    protected CMonoid<GMonomial<V>> mm;

    /**
     * Create the ring using the help of some coefficient ring and monomial
     * monoid.
     * @param coeffRing This ring operates on coefficients of type C.
     * @param monomialMonoid This monoid operates on the monomials using V.
     */
    public SimpleGPolyFlatRing(
            final Semiring<C> coeffRing,
            final CMonoid<GMonomial<V>> monomialMonoid) {
        this.rc = coeffRing;
        this.mm = monomialMonoid;
    }

    /**
     * Adds the two GPolys and returns the result.
     *
     * @param first The first addend.
     * @param second The second addend.
     * @return A new polynomial which is the sum first + second.
     */
    @Override
    public Map<GMonomial<V>, C> plus(final Map<GMonomial<V>, C> first, final Map<GMonomial<V>, C> second) {
        if (first.equals(this.zero())) {
            if (second.containsKey(this.mm.neutral())) {
                return second;
            } else {
                return this.plus(second, this.zero());
            }
        } else if (second.equals(this.zero())) {
            if (first.containsKey(this.mm.neutral())) {
                return first;
            } else {
                return this.plus(first, this.zero());
            }
        }
        // to be returned
        Map<GMonomial<V>, C> result = new LinkedHashMap<GMonomial<V>, C>();

        // temporary variable that contains the sum of two coefficients.
        C sum;

        // first consider all mappings of monomials to coefficients
        // of "first"
        C zero = this.rc.zero();
        for (Map.Entry<GMonomial<V>, C> entry : first.entrySet()) {
            GMonomial<V> key = entry.getKey();

            // if a key occurs in both GPolys, we do the addition.
            C currentCoeff = second.get(key);
            if (currentCoeff != null) {
                C value = entry.getValue();
                if (value == zero) {
                    sum = currentCoeff;
                } else if (currentCoeff == zero) {
                    sum = value;
                } else {
                    sum = this.rc.plus(value, currentCoeff);
                }
                if (key.equals(this.mm.neutral())
                        || !sum.equals(this.rc.zero())) {
                    result.put(key, sum);
                }
            } else {
                // just include the old mapping of "first"
                result.put(key, entry.getValue());
            }
        }

        // then the ones in "second" which have not been considered so far
        for (Map.Entry<GMonomial<V>, C> entry : second.entrySet()) {
            GMonomial<V> key = entry.getKey();
            if (!first.containsKey(key)) {
                result.put(key, entry.getValue());
            }
        }
          return result;
    }

    /**
     * Multiplies the two GPolys and returns the result.
     *
     * @param first The first factor.
     * @param second The second factor.
     * @return the product of the two GPolys, first * second (not
     * necessarily second * first).
     */
    @Override
    public Map<GMonomial<V>, C> times(final Map<GMonomial<V>, C> first, final Map<GMonomial<V>, C> second) {
        // to be returned (as GPoly).
        Map<GMonomial<V>, C> result = new LinkedHashMap<GMonomial<V>, C>();

        // temporary variable needed for the product of two monomials.
        GMonomial<V> newKey;
        // temporary variable needed for the product of two GPolys.
        C newValue;

        for (Map.Entry<GMonomial<V>, C> entry1 : first.entrySet()) {
            GMonomial<V> key1 = entry1.getKey();
            C value1 = entry1.getValue();
            for (Map.Entry<GMonomial<V>, C> entry2 : second.entrySet()) {
                newKey = this.mm.op(key1, entry2.getKey());
                C value2 = entry2.getValue();
                C zero = this.rc.zero();
                if (zero == value1 || zero == value2) {
                    newValue = zero;
                } else {
                    newValue = this.rc.times(value1, value2);
                }
                C oldValue = result.get(newKey);
                if (oldValue != null) {
                    newValue = this.rc.plus(newValue, oldValue);
                }
                if (newKey.equals(this.mm.neutral())
                        || !newValue.equals(this.rc.zero())) {
                    result.put(newKey, newValue);
                }
            }
        }
        return result;
    }

    /**
     * ACTUAL RINGS ONLY.
     * @param minuend Minuend.
     * @param subtrahend Subtrahend.
     * @return minuend - subtrahend.
     */
    @Override
    public Map<GMonomial<V>, C> minus(
            final Map<GMonomial<V>, C> minuend,
            final Map<GMonomial<V>, C> subtrahend) {
        if (!this.rc.isRing()) {
            throw new UnsupportedOperationException("Subtraction is supported only by actual rings.");
        }
        if (subtrahend.equals(this.zero())) {
            return minuend;
        }
        // to be returned
        Map<GMonomial<V>, C> result = new LinkedHashMap<GMonomial<V>, C>();

        // temporary variable that contains the difference of two coefficients.
        C diff;

        // this typecast is always valid
        Ring<C> rc = (Ring<C>)this.rc;

        // first consider all mappings of monomials to coefficients
        // of "minuend"
        for (Map.Entry<GMonomial<V>, C> entry : minuend.entrySet()) {
            GMonomial<V> key = entry.getKey();

            // if a key occurs in both GPolys, we do the subtraction.
            C currentCoeff = subtrahend.get(key);
            if (currentCoeff != null) {
                diff = rc.minus(entry.getValue(), currentCoeff);
                if (key.equals(this.mm.neutral())
                        || !diff.equals(this.rc.zero())) {
                    result.put(key, diff);
                }
            } else {
                // just include the old mapping of "first"
                result.put(key, entry.getValue());
            }
        }

        // then the ones in "second" which have not been considered so far
        for (Map.Entry<GMonomial<V>, C> entry : subtrahend.entrySet()) {
            GMonomial<V> key = entry.getKey();
            if (!minuend.containsKey(key)) {
                result.put(key, rc.getInverse(entry.getValue()));
            }
        }
        return result;
    }

    /**
     * ACTUAL RINGS ONLY.
     * @param target find the inverse of this.
     * @return the inverse of target wrt. "+".
     */
    @Override
    public Map<GMonomial<V>, C> getInverse(final Map<GMonomial<V>, C> target) {
        if (!this.rc.isRing()) {
            throw new UnsupportedOperationException("This is but a semiring and has no inverses");
        }
        Map<GMonomial<V>, C> result = new LinkedHashMap<GMonomial<V>, C>();
        Ring<C> rc = (Ring<C>)this.rc;
        for (Map.Entry<GMonomial<V>, C> entry : target.entrySet()) {
            result.put(entry.getKey(), rc.getInverse(entry.getValue()));
        }
        return result;
    }

    /**
     * @return A polynomial that is neutral wrt. addition as defined above.
     */
    @Override
    public Map<GMonomial<V>, C> zero() {
        // here a map without any monomial is good.
        return ImmutableCreator.create(Collections.<GMonomial<V>, C>emptyMap());
    }

    /**
     * @return A polynomial that is neutral wrt. multiplication as defined
     * above.
     */
    @Override
    public Map<GMonomial<V>, C> one() {
        // as the multiplication in this ring uses multiplication over the
        // coefficients and monomials, the corresponding one-elements should be
        // used.
        return Collections.singletonMap(this.mm.neutral(), this.rc.one());
    }

    /**
     * @return the monoid that is used internally.
     */
    @Override
    public CMonoid<GMonomial<V>> getMonoid() {
        return this.mm;
    }

    /**
     * @return the ring for coefficients that is used internally.
     */
    @Override
    public Semiring<C> getRing() {
        return this.rc;
    }

    /**
     * @return true if this is an actual ring (and not merely a semiring).
     */
    @Override
    public boolean isRing() {
        return this.rc.isRing();
    }

    @Override
    public SpecializedGInterpretation getSpecializedGInterpretation() {
        return DummySpecializedGInterpretation.create();
    }

}
