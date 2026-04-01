/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import immutables.*;

/**
 * This class only holds the data representing a monomial (without coefficient).
 * The monoid operations are defined in e.g. GMonomialMonoid.
 * @param <V> The type of the variables.
 */
public class GMonomial<V extends GPolyVar> implements Immutable, Exportable, Comparable<GMonomial<V>> {
    /**
     * For each variable in this monomial store the corresponding exponent.
     */
    private final ImmutableMap<V, BigInteger> exponents;

    /**
     * Remember if the hash value is correct.
     */
    private boolean hashValid;

    /**
     * Cache the hash value.
     */
    private int hashValue;

    /**
     * Generates an empty GMonomial, by convention the empty mapping.
     */
    public GMonomial() {
        this.exponents =
            ImmutableCreator.create(Collections.<V, BigInteger>emptyMap());
        this.hashValid = false;
    }

    /**
     * Creates an GMonomial with the same variable-to-exponents mapping
     * as exp. Returns an empty GMonomial if exp == null.
     * Exponents will not be modified by this class, but one must not
     * modify it outwards either. Otherwise, give a copy to the constructor.
     *
     * exp may not contain variables with exponents <= 0.
     * @param exp The mapping of variables to exponents.
     */
    public GMonomial(final Map<V, BigInteger> exp) {
        if (exp == null) {
            this.exponents =
                ImmutableCreator.create(Collections.<V, BigInteger>emptyMap());
        } else {
            if (Globals.useAssertions) {
                for (Map.Entry<V, BigInteger> entry : exp.entrySet()) {
                    // empty variable names create confusion
                    assert (entry.getKey().toString().length() > 0);
                    // all exponents should be strictly positive
                    assert (entry.getValue().signum() > 0);
                }
            }
            this.exponents = ImmutableCreator.create(exp);
        }
        this.hashValid = false;
    }

    /**
     * Create a GMonomial only consisting of var^1.
     * @param var The variable.
     */
    public GMonomial(final V var) {
        if (Globals.useAssertions) {
            // empty variable names create confusion
            assert (var.toString().length() > 0);
        }
        Map<V, BigInteger> exp =
            Collections.singletonMap(var, BigInteger.ONE);
        this.exponents = ImmutableCreator.create(exp);
    }

    /**
     * @return some readable string representation.
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (Map.Entry<V, BigInteger> entry : this.exponents.entrySet()) {
            if (!first) {
                sb.append("*");
            }
            first = false;
            sb.append(entry.getKey());
            if (entry.getValue().compareTo(BigInteger.ONE) != 0) {
                sb.append("^");
                sb.append(entry.getValue());
            }
        }
        return sb.toString();
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder buffer = new StringBuilder(5*this.exponents.size());
        SortedMap<String, BigInteger> sortedAndExportedExponents;
        sortedAndExportedExponents = new TreeMap<String, BigInteger>();
        Iterator<Entry<V, BigInteger>> expIter;
        expIter = this.exponents.entrySet().iterator();

        // export 'em and sort 'em
        while (expIter.hasNext()) {
            Map.Entry<V, BigInteger> entry = expIter.next();
            V key = entry.getKey();
            String varExport = key.export(o);
            sortedAndExportedExponents.put(varExport, entry.getValue());
        }

        // now put 'em together in sorted order
        Iterator<Entry<String, BigInteger>> sortedIter;
        sortedIter = sortedAndExportedExponents.entrySet().iterator();
        while (sortedIter.hasNext()) {
            Map.Entry<String, BigInteger> entry = sortedIter.next();
            String key = entry.getKey();
            buffer.append(key);
            BigInteger power = entry.getValue();
            if (power.compareTo(BigInteger.ONE) > 0) {
                buffer.append(o.sup(power.toString()));
            }
            if (sortedIter.hasNext()) {
                buffer.append(o.multSign());
            }
        }

        return buffer.toString();
    }

    /**
     * @return the exponents.
     */
    public Map<V, BigInteger> getExponents() {
        return this.exponents;
    }

    /**
     * @param key
     * @return the exponent corresponding to the key
     */
    public BigInteger getExponent(V key) {
        return this.exponents.get(key);
    }

    /**
     * @return the degree of this, i.e., the sum of all exponents
     */
    public BigInteger getDegree() {
        BigInteger res = BigInteger.ZERO;
        for (Entry<V, BigInteger> power : this.exponents.entrySet()) {
            BigInteger exp = power.getValue();
            res = res.add(exp);
        }
        return res;
    }

    /**
     * Return the cached hash code, calculate it when necessary.
     * @return The hash code.
     */
    @Override
    public int hashCode() {
        if (this.hashValid) {
            return this.hashValue;
        }
        this.computeHashValue();
        return this.hashValue;
    }

    /**
     * Compute the hash value and store it in the hash value cache.
     */
    private void computeHashValue() {
        this.hashValue = this.exponents.hashCode();
        this.hashValid = true;
    }

    /**
     * Find out if the two objects are equal by using the hashcode and
     * comparing the exponents if necessary.
     * @param o The object to compare with.
     * @return true if the two monomials are equal.
     */
    @Override
    public boolean equals(final Object o) {
        GMonomial other;

        if (!(o instanceof GMonomial)) {
            return false;
        }
        other = (GMonomial) o;

        // profit from our cached hash value
        if (other.hashCode() != this.hashCode()) {
            return false;
        }
        return (other.exponents.equals(this.exponents));
    }

    /**
     * Enable comparison so that the string representation of polynomials shows
     * the variable parts in ordered form (0 + ...x1 + ...x2).
     * @param o the object to compare with.
     * @return a integer value describing if the other object is <, =, > to
     * this.
     */
    @Override
    public int compareTo(final GMonomial<V> o) {
        // TODO this is too time consuming
        if (this.equals(o)) {
            return 0;
        }
        return this.toString().compareTo(o.toString());
    }
}
