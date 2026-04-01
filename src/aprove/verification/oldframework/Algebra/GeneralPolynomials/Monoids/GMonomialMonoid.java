/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * This monoid implementation is able to multiply two monomials.
 * xy * x^2yz = x^3y^2z.
 *
 * @version $Id$
 * @param <V> The type of the variables.
 */
public class GMonomialMonoid<V extends GPolyVar>
    implements CMonoid<GMonomial<V>> {
    /**
     * Cache operations.
     */
    private Map<Set<GMonomial<V>>, GMonomial<V>> cache =
        new HashMap<Set<GMonomial<V>>, GMonomial<V>>();
    /**
     * This will always be the neutral element for this monoid.
     */
    private GMonomial<V> neutral = new GMonomial<V>();

    /**
     * Computes the product of two GMonomials.
     *
     * @param first The first factor.
     * @param second The second factor.
     * @return the product first * second (not necessarily second * first).
     */
    @Override
    public GMonomial<V> op(final GMonomial<V> first,
            final GMonomial<V> second) {
        if (this.neutral.equals(first)) {
            return second;
        } else if (this.neutral.equals(second)) {
            return first;
        }
        Set<GMonomial<V>> set = new LinkedHashSet<GMonomial<V>>(2);
        set.add(first);
        set.add(second);
        if (this.cache.containsKey(set)) {
            return this.cache.get(set);
        }

        Map<V, BigInteger> firstExponents = first.getExponents();
        Map<V, BigInteger> secondExponents = second.getExponents();
        // to be returned as GMonomial
        Map<V, BigInteger> result = new LinkedHashMap<V, BigInteger>();

        // temporary variable for the exponent of the current variable part
        BigInteger currentExponent;

        // first consider all map entries that occur in "first"
        for (Map.Entry<V, BigInteger> entry : firstExponents.entrySet()) {
            V indefinite = entry.getKey();
            BigInteger power = entry.getValue();

            currentExponent = secondExponents.get(indefinite);
            if (currentExponent == null) {
                currentExponent = BigInteger.ZERO;
            }

            power = power.add(currentExponent);
            if (power.signum() != 0) {
                result.put(indefinite, power);
            }
        }

        // then those that only occur in "second"
        for (Map.Entry<V, BigInteger> entry : secondExponents.entrySet()) {
            V indefinite = entry.getKey();
            if (!firstExponents.containsKey(indefinite)) {
                result.put(indefinite, entry.getValue());
            }
        }
        GMonomial<V> resultMonomial = new GMonomial<V>(result);
        this.cache.put(set, resultMonomial);
        return resultMonomial;
    }

    /**
     * Multiply the two given GMonomials.
     * "Times" is a more intuitive name for the monoid operation op.
     * @param first The first factor.
     * @param second The second factor.
     * @return The product first * second.
     */
    public GMonomial<V> times(final GMonomial<V> first,
            final GMonomial<V> second) {
        return this.op(first, second);
    }

    /**
     * @return the neutral element of multiplikation.
     */
    @Override
    public GMonomial<V> neutral() {
        return this.neutral;
    }
}
