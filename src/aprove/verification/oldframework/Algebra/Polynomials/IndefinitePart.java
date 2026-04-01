package aprove.verification.oldframework.Algebra.Polynomials;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Carsten Fuhs
 * @version $Id$
 *
 * IndefinitePart encapsulates the part of a monomial which
 * consists of a product of indefinite atoms (variables or coefficients,
 * depending on context). Example: x^2*y^3
 *
 * Note for the interface Comparable: IndefinitePart.compareTo conducts a
 * comparison on /syntactic/ level, not on arithmetic level (otherwise,
 * "a" and "b" would be incomparable, which would violate the contract of
 * Comparable.
 */
public class IndefinitePart implements Immutable, Exportable,
Comparable<IndefinitePart> {

    // map the variables to their exponents,
    private final ImmutableMap<String, Integer> exponents;

    private int hashValue; // cache for the hash value
    private boolean hashValid; // has the hash value already been computed?

    public static final IndefinitePart ONE = new IndefinitePart();

    // the empty IndefinitePart is the neutral element of multiplication (one)

    /**
     * Generates an empty IndefinitePart, by convention the empty mapping. Use
     * IndefinitePart.ONE instead of this constructor.
     */
    private IndefinitePart() {
        this.exponents =
            ImmutableCreator.create(Collections.<String, Integer> emptyMap());
        this.hashValid = false;
    }

    /**
     * Creates an IndefinitePart with the same variable-to-exponents mapping as
     * exponents. Returns an empty IndefinitePart if exponents == null.
     * Exponents will not be modified by this class, but one must not modify it
     * outwards either. Otherwise, give a copy to the constructor.
     * @param exponents the mapping of variables to exponents
     */
    IndefinitePart(final Map<String, Integer> exponents) {
        if (exponents == null) {
            this.exponents =
                ImmutableCreator.create(Collections.<String, Integer> emptyMap());
        } else {
            this.exponents = ImmutableCreator.create(exponents);
        }
        this.hashValid = false;
    }

    /**
     * Creates an IndefinitePart which is equivalent to indefinite.
     * @param indefinite the indefinite of which this is supposed to consist
     */
    IndefinitePart(final String indefinite) {
        final Map<String, Integer> exp =
            Collections.singletonMap(indefinite, 1);
        this.exponents = ImmutableCreator.create(exp);
        this.hashValid = false;
    }

    /**
     * Creates an IndefinitePart equivalent to the product of the elements of
     * indefinites.
     * @param indefinites this is supposed to consist of them
     */
    IndefinitePart(final Set<String> indefinites) {
        Map<String, Integer> exponents;
        exponents = new LinkedHashMap<String, Integer>(indefinites.size());
        for (final String indef : indefinites) {
            exponents.put(indef, 1);
        }
        this.exponents = ImmutableCreator.create(exponents);
        this.hashValid = false;
    }

    /**
     * Creates a new IndefinitePart with the entries of <code>exponents</code>.
     * @param exponents maps indefinites to their corresponding exponent
     * @return a new IndefinitePart that corresponds to exponents
     */
    public static IndefinitePart create(final Map<String, Integer> exponents) {
        return new IndefinitePart(exponents);
    }

    public static IndefinitePart create(final String indef, final Integer power) {
        return new IndefinitePart(Collections.singletonMap(indef, power));
    }

    /**
     * Generates an IndefinitePart from a Polynomial which must consist of a
     * single Monomial which in turn only contains variables and their
     * corresponding exponents. Such Polynomials can be obtained e.g. by taking
     * the first component of the pair that results from calling
     * Monomial.splitCoefficient(...).
     * @param poly the Polynomial of type x1^k1 * ... * xn^kn
     * @return the corresponding IndefinitePart (or null if poly == null)
     */
    public static IndefinitePart toIndefinitePart(final Polynomial poly) {
        IndefinitePart result; // to be returned

        if (poly == null) {
            return null;
        }
        result =
            new IndefinitePart(new LinkedHashMap<String, Integer>(
                poly.getFirst().exponents));
        return result;
    }

    /**
     * Get the exponent of an indefinite.
     * @param indefinite the indefinite (coefficient or variable)
     * @return the exponent with which the indefinite occurs here or zero if it
     * does not occur.
     */
    public Integer getExponent(final String indefinite) {
        final Integer result = this.exponents.get(indefinite);
        return result == null ? 0 : result;
    }

    /**
     * Returns the (immutable) mapping of variables to their exponents. Needed
     * by the conversion methods that occur e.g. in SimplePolynomial (one must
     * be able to get hold of the variables of the corresponding
     * IndefinitePart). Also needed for SatSearch.
     * @return the (immutable) mapping of variables to their exponents
     */
    public ImmutableMap<String, Integer> getExponents() {
        return this.exponents;
    }

    /**
     * @return the degree of this, i.e., the sum of all exponents
     */
    public int getDegree() {
        int res = 0;
        for (final Entry<String, Integer> power : this.exponents.entrySet()) {
            final int exp = power.getValue();
            res += exp;
        }
        return res;
    }

    /**
     * @param x - an indefinite that may or may not occur in this
     * @return the first derivative of this with respect to x (new numerical
     * coeff and resulting monomial)
     */
    public Pair<Integer, IndefinitePart> deriveWRT(final String x) {
        final Integer power = this.exponents.get(x);
        if (power == null) {
            return new Pair<Integer, IndefinitePart>(0, IndefinitePart.ONE);
        }
        final Map<String, Integer> resIP =
            new LinkedHashMap<String, Integer>(this.exponents);
        final int powerInt = power.intValue();
        if (powerInt == 1) {
            resIP.remove(x);
        } else {
            resIP.put(x, powerInt - 1);
        }
        return new Pair<Integer, IndefinitePart>(power, IndefinitePart.create(resIP));
    }

    /**
     * Computes the product of this and another IndefinitePart.
     * @param factor the IndefinitePart to be multiplied to this
     * @return the product of this and factor
     */
    public IndefinitePart times(final IndefinitePart factor) {
        final Map<String, Integer> result =
            new LinkedHashMap<String, Integer>();
        // to be returned (as IndefinitePart)

        int currentExponent; // temporary variable for the exponent of the
        // current indefinite

        // first consider all Map Entries that occur in this ...
        for (final Map.Entry<String, Integer> entry : this.exponents.entrySet()) {
            final String indefinite = entry.getKey();
            Integer power = entry.getValue();

            currentExponent = factor.getExponent(indefinite);
            power += currentExponent;
            result.put(indefinite, power);
        }

        // ... then those that /only/ occur in factor
        for (final Map.Entry<String, Integer> entry : factor.exponents.entrySet()) {
            final String indefinite = entry.getKey();
            if (!this.exponents.containsKey(indefinite)) {
                result.put(indefinite, entry.getValue());
            }
        }
        return new IndefinitePart(result);
    }

    /**
     * Computes the product of several IndefiniteParts..
     * @param factors the IndefiniteParts to be multiplied
     * @return the product
     */
    public static IndefinitePart times(final Collection<IndefinitePart> factors) {
        final Map<String, Integer> result =
            new LinkedHashMap<String, Integer>();
        // to be returned (as IndefinitePart)

        for (final IndefinitePart factor : factors) {
            for (final Map.Entry<String, Integer> entry : factor.exponents.entrySet()) {
                final String indefinite = entry.getKey();
                final Integer power = entry.getValue();

                if (result.get(indefinite) != null) {
                    result.put(indefinite, result.get(indefinite) + power);
                } else {
                    result.put(indefinite, power);
                }
            }

        }
        return new IndefinitePart(result);
    }

    /**
     * Computes the "square root" of this.
     *
     * @return a result pair such that pair.x * pair.x * pair.y = this and
     *  pair.y only contains indefinites at exponent 1
     */
    public Pair<IndefinitePart, IndefinitePart> sqrt() {
        final LinkedHashMap<String, Integer> rootExp, restExp;
        rootExp = new LinkedHashMap<>();
        restExp = new LinkedHashMap<>();
        for (final Entry<String, Integer> xToPower : this.exponents.entrySet()) {
            final String indef = xToPower.getKey();
            final int power = xToPower.getValue();
            final int halfPower = power / 2;
            if (halfPower > 0) {
                rootExp.put(indef, halfPower);
            }
            if (power % 2 == 1) {
                restExp.put(indef, 1);
            }
        }
        final IndefinitePart resX = new IndefinitePart(rootExp);
        final IndefinitePart resY = new IndefinitePart(restExp);
        return new Pair<>(resX, resY);
    }

    /**
     * Returns the specialization of this in which all indefinites are assigned
     * the constant <code>value</code>.
     * @param value to be assigned to each indefinite
     * @return the number resulting from assigning value to each indefinite of
     * this
     */
    public BigInteger setAllIndefinitesTo(final BigInteger value) {
        if (this.equals(IndefinitePart.ONE)) {
            return BigInteger.ONE;
        }
        int totalPower = 0;
        for (final Integer power : this.exponents.values()) {
            totalPower += power;
        }
        final BigInteger result = value.pow(totalPower);
        return result;
    }

    /**
     * Replaces the indefinite powers of this by their numerical values as
     * indicated by values.
     * @param values indefinite-to-value mapping, not necessarily for all
     * indefinites of this.
     * @return a Pair of the IndefinitePart which consists of * the maximal
     * sub-IndefinitePart of this whose indefinites are not in values.keySet() *
     * the number obtained by replacing indefinites by their values as indicated
     * by values; (IndefinitePart.ONE, ZERO) in case some indefinite of this is
     * mapped to 0.
     */
    Pair<IndefinitePart, BigInteger> specialize(final Map<String, BigInteger> values) {
        final Map<String, Integer> exponents =
            new LinkedHashMap<String, Integer>();
        BigInteger factor = BigInteger.ONE;
        for (final Map.Entry<String, Integer> entry : this.exponents.entrySet()) {
            final String key = entry.getKey();
            final BigInteger assignedValue = values.get(key);
            if (assignedValue == null) { // values does not know the current indefinite
                exponents.put(key, entry.getValue());
            } else if (assignedValue.signum() == 0) { // the whole product will be 0
                return new Pair<IndefinitePart, BigInteger>(IndefinitePart.ONE,
                    BigInteger.ZERO);
            } else {
                final BigInteger keyToThePower =
                    assignedValue.pow(entry.getValue());
                factor = factor.multiply(keyToThePower);
                //factor *= AProVEMath.power(assignedValue, entry.getValue());
            }
        }
        return new Pair<IndefinitePart, BigInteger>(new IndefinitePart(
            exponents), factor);
    }

    /**
     * Replaces the indefinite powers of this by their numerical values as
     * indicated by values.
     * @param values indefinite-to-value mapping, not necessarily for all
     * indefinites of this; values can be indefinites or numbers as encapsulated
     * by GENode
     * @return a Pair of the IndefinitePart which consists of * the
     * IndefinitePart that results from applying the substitution values on this
     * where mappings to numerical GENodes are ignored * the number obtained by
     * replacing indefinites by their values as indicated by values where
     * mappings to non-numerical GENodes are ignored (IndefinitePart.ONE, 0) in
     * case some indefinite of this is mapped to 0.
     */
    Pair<IndefinitePart, BigInteger> specializeGENode(final Map<String, GENode> values) {
        final Map<String, Integer> exponents =
            new LinkedHashMap<String, Integer>();
        BigInteger factor = BigInteger.ONE;
        for (final Map.Entry<String, Integer> entry : this.exponents.entrySet()) {
            final String key = entry.getKey();
            final GENode assignedValue = values.get(key);
            if (assignedValue == null) { // values does not know the current indefinite
                exponents.put(key, entry.getValue());
            } else if (assignedValue.isNumerical()) {
                if (assignedValue.number.signum() == 0) { // the whole product will be 0
                    return new Pair<IndefinitePart, BigInteger>(
                        IndefinitePart.ONE, BigInteger.ZERO);
                } else {
                    factor =
                        factor.multiply(assignedValue.number.pow(entry.getValue()));
                }
            } else { // assignedValue is indefinite
                final Integer oldExponent =
                    exponents.get(assignedValue.indefinite);
                if (oldExponent == null) { // assignedValue.indefinite unknown by exponents so far
                    exponents.put(assignedValue.indefinite, entry.getValue());
                } else {
                    exponents.put(assignedValue.indefinite, entry.getValue()
                        + oldExponent);
                }
            }
        }
        return new Pair<IndefinitePart, BigInteger>(new IndefinitePart(
            exponents), factor);
    }

    /**
     * @param values maps indefinites to integer intervals with possible values,
     * must assign non-null values to all indefinites of this
     * @return the maximum value this can take given values
     */
    BigInteger max(final Map<String, BigIntegerInterval> values) {
        BigInteger result = BigInteger.ONE;
        for (final Map.Entry<String, Integer> entry : this.exponents.entrySet()) {
            final BigInteger assignedValue = values.get(entry.getKey()).max;
            if (assignedValue.signum() == 0) {
                return BigInteger.ZERO;
            } else {
                result = result.multiply(assignedValue.pow(entry.getValue()));
            }
        }
        return result;
    }

    /**
     * @param values maps indefinites to integer intervals with possible values,
     * must assign non-null values to all indefinites of this
     * @return the minimum value this can take given values
     */
    BigInteger min(final Map<String, BigIntegerInterval> values) {
        BigInteger result = BigInteger.ONE;
        for (final Map.Entry<String, Integer> entry : this.exponents.entrySet()) {
            final BigInteger assignedValue = values.get(entry.getKey()).min;
            if (assignedValue.signum() == 0) {
                return BigInteger.ZERO;
            } else {
                result = result.multiply(assignedValue.pow(entry.getValue()));
            }
        }
        return result;
    }

    /**
     * @return a Set of all possible splits of this which follow the pattern
     * (this with one indefinite removed, the removed indefinite, the power with
     * which the removed indefinite occurs in this); consistently, the empty Set
     * is returned if this is empty.
     */
    public Set<Triple<IndefinitePart, String, Integer>> getSplits() {
        final Set<Triple<IndefinitePart, String, Integer>> result =
            new LinkedHashSet<Triple<IndefinitePart, String, Integer>>();
        for (final Map.Entry<String, Integer> entry : this.exponents.entrySet()) {
            final String key = entry.getKey();
            final Map<String, Integer> exponents =
                new LinkedHashMap<String, Integer>(this.exponents);
            exponents.remove(key);
            result.add(new Triple<IndefinitePart, String, Integer>(
                new IndefinitePart(exponents), key, entry.getValue()));
        }
        return result;
    }

    /**
     * Counts how many times a product a_i * a_j or a_i^2 occurs in this and
     * increments the values of the mapping products accordingly.
     * @param products mapping [StringPair -> Integer] which keeps track of how
     * many times a product of two variables (stored in the key of the mapping)
     * has been observed. The corresponding values are incremented by the number
     * of sightings of the respective products in this. Note that the second
     * indefinite of the StringPair is never smaller than the first one with
     * respect to the natural order of String.
     */
    public void getProducts(final Map<StringPair, Integer> products) {
        for (final Map.Entry<String, Integer> exponent1 : this.exponents.entrySet()) {
            final String indefinite1 = exponent1.getKey();
            final int power1 = exponent1.getValue();

            // check for squares
            if (power1 > 1) {
                this.updateProducts(new StringPair(indefinite1, indefinite1),
                    power1 / 2, products);
            }

            // count binary products of different indefinites
            for (final Map.Entry<String, Integer> exponent2 : this.exponents.entrySet()) {
                final String indefinite2 = exponent2.getKey();

                // don't look at any pair twice
                if (indefinite1.compareTo(indefinite2) < 0) {
                    final int minPower = Math.min(power1, exponent2.getValue());
                    if (Globals.useAssertions) {
                        assert minPower > 0;
                    }
                    this.updateProducts(
                        new StringPair(indefinite1, indefinite2), minPower,
                        products);
                }
            }
        }
    }

    /**
     * Increments the count of pair in products by value. TODO make up your mind
     * on whether you want to store 0 in products (currently 0 is stored as well
     * instead of just removing the entry)
     * @param pair a pair of indefinites
     * @param value the value by which the count of pair is to be incremented in
     * products
     * @param products mapping [StringPair -> Integer], used for keeping track
     * of how many times a product of two variables has been seen
     */
    private void updateProducts(final StringPair pair,
        final int value,
        final Map<StringPair, Integer> products) {
        final Integer count = products.get(pair);
        if (count == null) {
            if (Globals.useAssertions) {
                // storing that some product occurs < 0 times
                // would seem to be kind of a bad idea.
                assert value >= 0;
            }
            if (value > 0) {
                products.put(pair, value);
            }
        } else {
            final int sum = value + count;
            if (Globals.useAssertions) {
                assert sum >= 0;
            }
            if (sum == 0) {
                // keep the map small
                products.remove(pair);
            } else {
                products.put(pair, sum);
            }
        }
    }

    /**
     * Replaces x^2 by z in this. products is modified accordingly in the
     * process.
     * @param x x^2 is to be replaced in this
     * @param z replacement for x^2
     * @param products keeps track of how often each product of two indefinites
     * occurs in the system (map StringPair -> Integer), is modified to suit a
     * replacement of this by the returned IndefinitePart; (x, x) is assumed not
     * to occur in products any more when replaceSquares(...) is called
     */
    public IndefinitePart replaceSquares(final String x,
        final String z,
        final Map<StringPair, Integer> products) {

        if (Globals.useAssertions) {
            assert !x.equals(z);
            assert !this.exponents.containsKey(z);
        }

        final Integer xPowerInteger = this.exponents.get(x);
        if (xPowerInteger == null) {
            return this;
        }

        final int xPower = xPowerInteger;
        if (xPower < 2) {
            if (Globals.useAssertions) {
                assert xPower == 1;
            }
            return this;
        }

        Map<StringPair, Integer> oldProducts; // for debugging
        if (false && Globals.DEBUG_FUHS) {
            oldProducts = new LinkedHashMap<StringPair, Integer>(products);
        }

        final Map<String, Integer> result =
            new LinkedHashMap<String, Integer>(this.exponents);
        final int xPowerHalf = xPower / 2;

        this.updateProducts(new StringPair(z, z), xPowerHalf / 2, products);

        if (xPower % 2 == 0) {
            for (final Map.Entry<String, Integer> entry : result.entrySet()) {
                final String key = entry.getKey();
                final int keyPower = entry.getValue();

                if (!key.equals(x)) {
                    this.updateProducts(new StringPair(z, key),
                        Math.min(xPowerHalf, keyPower), products);
                    this.updateProducts(new StringPair(x, key),
                        -Math.min(xPower, keyPower), products);
                }
                // x^2 has already been removed before the method was called.
            }
            result.remove(x);
        } else {
            for (final Map.Entry<String, Integer> entry : result.entrySet()) {
                final String key = entry.getKey();
                final int keyPower = entry.getValue();

                if (!key.equals(x)) {
                    this.updateProducts(new StringPair(x, key),
                        1 - Math.min(xPower, keyPower), products);
                    this.updateProducts(new StringPair(z, key),
                        Math.min(xPowerHalf, keyPower), products);
                } else {
                    // note that x^2 has already been removed before the method was called.

                    // x*z will occur exactly once in result!
                    this.updateProducts(new StringPair(x, z), 1, products);
                }
            }
            result.put(x, 1);
        }
        result.put(z, xPowerHalf);

        if (false && Globals.DEBUG_FUHS) {
            // The following arithmetic term had better hold:
            // \forall u where u != y and u != x :
            //     products_{at the beginning of the method} ( (u,x) ) - min (this.exponents(u), this.exponents(x))
            //  == products_{at the end of the method} ( (u,x) ) - min (result(u), result(x))
            // similar with swapped x and y.

            Integer resultX = result.get(x);
            if (resultX == null) {
                resultX = 0;
            }
            final int oldX = this.getExponent(x);

            for (final Entry<String, Integer> exp : this.exponents.entrySet()) {
                final String u = exp.getKey();
                if (!u.equals(x)) {
                    final int uPowerBefore = this.exponents.get(u);
                    final int uPowerAfter = result.get(u);
                    final StringPair uAndX = new StringPair(u, x);
                    Integer oldUandX = oldProducts.get(uAndX);
                    if (oldUandX == null) {
                        oldUandX = 0;
                    }
                    Integer newUandX = products.get(uAndX);
                    if (newUandX == null) {
                        newUandX = 0;
                    }

                    final int before = oldUandX - Math.min(uPowerBefore, oldX);
                    final int after = newUandX - Math.min(uPowerAfter, resultX);
                    assert before == after;
                }
            }
        }

        return new IndefinitePart(result);
    }

    /**
     * Replaces x*y by z, returns the resulting IndefinitePart. Modifies
     * products accordingly.
     * @param x one of the two factors of the product which is to be replaced
     * @param y the other factor of the product which is to be replaced
     * @param z replacement for x*y
     * @param products keeps track of how often each product of two variables
     * occurs in the system (map StringPair -> Integer), is modified to suit the
     * changes that follow from replacing this by the returned IndefinitePart;
     * (x, y) is assumed not to occur in products any more when
     * replaceProducts(...) is called
     * @return the result of replacing x*y by z
     */
    public IndefinitePart replaceProducts(final String x,
        final String y,
        final String z,
        final Map<StringPair, Integer> products) {

        if (Globals.useAssertions) {
            assert !x.equals(y);
            assert !x.equals(z);
            assert !y.equals(z);
            assert !this.exponents.containsKey(z);
        }

        final Integer xPowerInteger = this.exponents.get(x);
        if (xPowerInteger == null) {
            return this;
        }
        final Integer yPowerInteger = this.exponents.get(y);
        if (yPowerInteger == null) {
            return this;
        }
        final int xPower = xPowerInteger;
        final int yPower = yPowerInteger;

        final int minPower = Math.min(xPower, yPower);
        if (Globals.useAssertions) {
            assert minPower > 0;
        }
        if (minPower > 1) {
            this.updateProducts(new StringPair(z, z), minPower / 2, products);
        }

        Map<StringPair, Integer> oldProducts; // for debugging
        if (false && Globals.DEBUG_FUHS) {
            oldProducts = new LinkedHashMap<StringPair, Integer>(products);
        }

        final Map<String, Integer> result =
            new LinkedHashMap<String, Integer>(this.exponents);

        if (xPower == yPower) {
            for (final Map.Entry<String, Integer> entry : result.entrySet()) {
                final String key = entry.getKey();
                if (key.equals(x) || key.equals(y)) {
                    continue;
                }
                final int keyPower = entry.getValue();

                this.updateProducts(new StringPair(x, key),
                    -Math.min(xPower, keyPower), products);
                this.updateProducts(new StringPair(y, key),
                    -Math.min(yPower, keyPower), products);
                this.updateProducts(new StringPair(z, key),
                    Math.min(minPower, keyPower), products);
            }

            this.updateProducts(new StringPair(x, x), -(xPower / 2), products);
            this.updateProducts(new StringPair(y, y), -(yPower / 2), products);

            result.remove(x);
            result.remove(y);
        } else if (xPower < yPower) {
            for (final Map.Entry<String, Integer> entry : result.entrySet()) {
                final String key = entry.getKey();
                if (key.equals(x)) {
                    continue;
                }
                if (key.equals(y)) {
                    // y*z will newly occur in result!
                    // e.g. x^4*y^9 will become y^5*z^4.
                    this.updateProducts(new StringPair(y, z),
                        Math.min(minPower, yPower - minPower), products);
                    continue;
                }
                final int keyPower = entry.getValue();

                this.updateProducts(new StringPair(x, key),
                    -Math.min(xPower, keyPower), products);
                this.updateProducts(
                    new StringPair(y, key),
                    Math.min(yPower - xPower, keyPower)
                    - Math.min(yPower, keyPower), products);
                this.updateProducts(new StringPair(z, key),
                    Math.min(minPower, keyPower), products);
            }

            this.updateProducts(new StringPair(x, x), -(xPower / 2), products);
            this.updateProducts(new StringPair(y, y), ((yPower - xPower) / 2)
                - (yPower / 2), products);

            result.remove(x);
            result.put(y, yPower - xPower);
        } else {
            for (final Map.Entry<String, Integer> entry : result.entrySet()) {
                final String key = entry.getKey();
                if (key.equals(y)) {
                    continue;
                }
                if (key.equals(x)) {
                    // x*z will newly occur in result!
                    // e.g. x^7*y^4 will become x^3*z^4.
                    this.updateProducts(new StringPair(x, z),
                        Math.min(minPower, xPower - minPower), products);
                    continue;
                }
                final int keyPower = entry.getValue();

                this.updateProducts(
                    new StringPair(x, key),
                    Math.min(xPower - yPower, keyPower)
                    - Math.min(xPower, keyPower), products);
                this.updateProducts(new StringPair(y, key),
                    -Math.min(yPower, keyPower), products);
                this.updateProducts(new StringPair(z, key),
                    Math.min(minPower, keyPower), products);
            }

            this.updateProducts(new StringPair(x, x), ((xPower - yPower) / 2)
                - (xPower / 2), products);
            this.updateProducts(new StringPair(y, y), -(yPower / 2), products);

            result.put(x, xPower - yPower);
            result.remove(y);
        }

        result.put(z, minPower);

        if (false && Globals.DEBUG_FUHS) {
            // The following arithmetic term had better hold:
            // \forall u where u != y (and probably also u != x) :
            //     products_{at the beginning of the method} ( (u,x) ) - min (this.exponents(u), this.exponents(x))
            //  == products_{at the end of the method} ( (u,x) ) - min (result(u), result(x))
            // similar with swapped x and y.

            Integer resultX = result.get(x);
            if (resultX == null) {
                resultX = 0;
            }
            final int oldX = this.getExponent(x);

            for (final Entry<String, Integer> exp : this.exponents.entrySet()) {
                final String u = exp.getKey();
                if ((!u.equals(x)) && (!u.equals(y))) {
                    final int uPowerBefore = this.exponents.get(u);
                    final int uPowerAfter = result.get(u);
                    final StringPair uAndX = new StringPair(u, x);
                    Integer oldUandX = oldProducts.get(uAndX);
                    if (oldUandX == null) {
                        oldUandX = 0;
                    }
                    Integer newUandX = products.get(uAndX);
                    if (newUandX == null) {
                        newUandX = 0;
                    }

                    final int before = oldUandX - Math.min(uPowerBefore, oldX);
                    final int after = newUandX - Math.min(uPowerAfter, resultX);
                    assert before == after;
                }
            }
        }
        return new IndefinitePart(result);
    }

    /**
     * Returns a renamed version of this.
     * @param renaming maps strings to strings (variables, not included, won't
     * be changed)
     * @return IndefinitePart
     */
    public IndefinitePart rename(final Map<String, String> renaming) {
        final LinkedHashMap<String, Integer> newExponents =
            new LinkedHashMap<>(this.exponents.size());
            for (final Entry<String, Integer> oldExponentPart : this.exponents.entrySet()) {
                final String newKey = renaming.get(oldExponentPart.getKey());
                if (!newExponents.containsKey(newKey)) {
                    newExponents.put(newKey, oldExponentPart.getValue());
                } else {
                    newExponents.put(newKey, oldExponentPart.getValue()
                        + newExponents.get(newKey));
                }
            }

            return IndefinitePart.create(newExponents);
    }

    /**
     * @return whether this is the empty IndefinitePart (equivalent to the
     * neutral element of multiplication, i.e., ONE)
     */
    public boolean isEmpty() {
        return this.exponents.isEmpty();
    }

    /**
     * Synonym for this.isEmpty().
     *
     * @return whether this is the empty IndefinitePart (equivalent to the
     * neutral element of multiplication, i.e., ONE)
     */
    public boolean isOne() {
        return this.isEmpty();
    }

    /**
     * @return how many different indefinites are in this
     */
    public int size() {
        return this.exponents.size();
    }

    /**
     * @return an ImmutableSet containing the indefinites that occur in this
     */
    public ImmutableSet<String> getIndefinites() {
        return ImmutableCreator.create(this.exponents.keySet());
    }

    /**
     * @param indefinite the indefinite for which we want to know whether it
     * occurs in this
     * @return whether the indefinite occurs in this
     */
    public boolean contains(final String indefinite) {
        return this.exponents.containsKey(indefinite);
    }

    /**
     * @param indefinites the indefinites for which we want to know whether they
     * all occur in this
     * @return whether all members of indefinites also occur in this
     */
    public boolean containsAll(final Set<String> indefinites) {
        return this.exponents.keySet().containsAll(indefinites);
    }

    /**
     * @param indefinite - indefinite for which we want to know whether it (and
     * no other one) occurs in this
     * @return whether exactly indefinite occurs in this
     */
    public boolean containsExactly(final String indefinite) {
        return this.exponents.size() == 1
            && this.exponents.containsKey(indefinite);
    }

    /**
     * @return null if this consists of 0 or >= 2 indefinites; the indefinite of
     * which this consists (regardless of its exponent), otherwise.
     */
    public String getTheOnlyIndefinite() {
        return this.exponents.size() == 1
            ? this.exponents.keySet().iterator().next() : null;
    }

    /**
     * Increments counts by one for each occurring indefinite.
     * @param counts keeps track of how often indefinites occur (without taking
     * into account the power at which they occur)
     */
    public void countIndefinites(final Map<String, Integer> counts) {
        for (final String indefinite : this.exponents.keySet()) {
            final Integer value = counts.get(indefinite);
            if (value == null) {
                counts.put(indefinite, 1);
            } else {
                counts.put(indefinite, value + 1);
            }
        }
    }

    /**
     * Increments counts by his exponent for each occurring indefinite.
     * @param counts keeps track of how often indefinites occur
     */
    public void countIndefinitesWithExponent(final Map<String, Integer> counts) {
        for (final String indefinite : this.exponents.keySet()) {
            final Integer value = counts.get(indefinite);
            if (value == null) {
                counts.put(indefinite, this.getExponent(indefinite));
            } else {
                counts.put(indefinite, value + this.getExponent(indefinite));
            }
        }
    }

    /**
     * @return whether this consists of exactly one indefinite at power 1
     */
    public boolean isIndefinite() {
        return (this.exponents.size() == 1)
            && (this.exponents.values().contains(1));
    }

    /**
     * @return whether this is linear (i.e., ONE or an indefinite)
     */
    public boolean isLinear() {
        return this.isEmpty() || this.isIndefinite();
    }

    /**
     * @return a_i if this is of form a_i^1; null otherwise
     */
    public String toIndefinite() {
        if (this.isIndefinite()) {
            return this.exponents.keySet().iterator().next();
        } else {
            return null;
        }
    }

    /**
     * @return the number of different indefinites that occur in this.
     */
    public int numberOfIndefinites() {
        return this.exponents.size();
    }

    /**
     * @param forbiddenIndefinites the indefinites that are not supposed to
     * occur in the returned IndefinitePart
     * @return an IndefinitePart with the same indefinite-to-exponent mapping as
     * this except that forbiddenIndefinites do not occur
     */
    public IndefinitePart removeIndefinites(final Set<String> forbiddenIndefinites) {
        final Map<String, Integer> result =
            new LinkedHashMap<String, Integer>(this.exponents);
        for (final String indefinite : forbiddenIndefinites) {
            result.remove(indefinite);
        }
        return new IndefinitePart(result);
    }

    /**
     * @param forbiddenIndefinite the indefinite that is not supposed to occur
     * in the returned IndefinitePart
     * @return an IndefinitePart with the same indefinite-to-exponent mapping as
     * this except that forbiddenIndefinite does not occur
     */
    public IndefinitePart removeIndefinite(final String forbiddenIndefinite) {
        final Map<String, Integer> result =
            new LinkedHashMap<String, Integer>(this.exponents);
        result.remove(forbiddenIndefinite);
        return new IndefinitePart(result);
    }

    /**
     * Creates a new IndefinitePart with the same variables as this but where
     * each variable occurs with exponent <code>exponent</code>.
     * @param exponent the exponent all variables of the returned IndefinitePart
     * are to be mapped to
     * @return the IndefinitePart in which the same indefinites occur as in
     * this, but with exponent <code>exponent</code>
     */
    public IndefinitePart copyWithFixedExponent(final int exponent) {
        final Map<String, Integer> result =
            new LinkedHashMap<String, Integer>(this.exponents.size());
        // to be returned (as IndefinitePart)

        for (final String indefinite : this.exponents.keySet()) {
            result.put(indefinite, exponent);
        }
        return new IndefinitePart(result);
    }

    /**
     * @param type the ConstraintType to be assigned to each of the resulting
     * SimplePolyConstraints
     * @return a Set of SimplePolyConstraints where each SimplePolyConstraint
     * consists of exactly one indefinite of this on the LHS and is of
     * ConstraintType type
     */
    Set<SimplePolyConstraint> getIndefinitesAsSimplePolyConstraints(final ConstraintType type) {
        final Set<SimplePolyConstraint> result =
            new LinkedHashSet<SimplePolyConstraint>(this.exponents.size());
        for (final String indefinite : this.exponents.keySet()) {
            final Map<String, Integer> exponents =
                Collections.<String, Integer> singletonMap(indefinite, 1);
            final IndefinitePart indefinitePart = new IndefinitePart(exponents);
            final Map<IndefinitePart, BigInteger> simpleMonomials =
                Collections.<IndefinitePart, BigInteger> singletonMap(
                    indefinitePart, BigInteger.ONE);
            final SimplePolyConstraint constraint =
                new SimplePolyConstraint(
                    SimplePolynomial.create(simpleMonomials), type);
            result.add(constraint);
        }
        return result;
    }

    /**
     * Computes the GCD (greatest common divisor) of this and exponents.
     * exponents == null is treated like an IndefinitePart in which all
     * conceivable indefinites occur at an infinite power (i.e., it does not
     * impose any constraints on the GCD), and thus a copy of this.exponents is
     * stored in exponents.
     * @param exponents the variable-to-exponent mapping regarding which the GCD
     * is to be computed
     * @return the GCD of this and exponents
     */
    public Map<String, Integer> computeGCD(final Map<String, Integer> exponents) {

        if (exponents == null) { // uninitialized
            return new LinkedHashMap<String, Integer>(this.exponents);
        } else {
            final Map<String, Integer> result =
                new LinkedHashMap<String, Integer>(exponents);
            final Iterator<Map.Entry<String, Integer>> entryIter =
                result.entrySet().iterator();
            Map.Entry<String, Integer> entry;
            while (entryIter.hasNext()) {
                entry = entryIter.next();
                final int entryValue = entry.getValue();
                final int value = this.getExponent(entry.getKey());
                if (value == 0) {
                    entryIter.remove();
                } else if (value < entryValue) {
                    entry.setValue(value);
                }
            }
            return result;
        }
    }

    /**
     * Divides this by denominator with all its exponents treated as reduced by
     * one and returns the resulting IndefinitePart. It is *required* that
     * denominator is a divisor of this, the result is undefined otherwise (and
     * Exceptions are likely in case IndefinitePart contains indefinites that do
     * not occur in this).
     * @param denominator the denominator by which this is to be "divided"
     * @return the resulting IndefinitePart: this divided by denominator whose
     * exponents are treated as reduced by one before dividing and whose
     * variables that do not occur in this are ignored
     */
    IndefinitePart divideWithDenominatorMinusOne(final IndefinitePart denominator) {
        final Map<String, Integer> result =
            new LinkedHashMap<String, Integer>(this.exponents);
        // to be returned (as IndefinitePart)

        for (final Map.Entry<String, Integer> entry : denominator.exponents.entrySet()) {
            String newIndefinite;
            int newPower;
            newIndefinite = entry.getKey();
            newPower = this.exponents.get(newIndefinite) - entry.getValue() + 1;
            result.put(newIndefinite, newPower);
        }
        return new IndefinitePart(result);
    }

    /**
     * Tries to divide this by demonimator and returns the result of the
     * division in case it could be performed successfully (that is, no
     * indefinite of the resulting IndefinitePart has a negative exponent),
     * otherwise, null is returned.
     * @param denominator the denominator by which this is to be divided
     * @return the result of the division; null iff the division would yield a
     * negative exponent for some indefinite
     */
    public IndefinitePart divide(final IndefinitePart denominator) {
        // a / b should not work!
        if (!this.exponents.keySet().containsAll(denominator.exponents.keySet())) {
            return null;
        }

        final Map<String, Integer> result =
            new LinkedHashMap<String, Integer>(this.exponents.size());

        // We only need to look at the indefinites in this because all of them
        // must occur in denominator, too (see above).
        for (final Map.Entry<String, Integer> entry : this.exponents.entrySet()) {
            final String indefinite = entry.getKey();
            final int oldPower = entry.getValue();
            final Integer denominatorExponent =
                denominator.exponents.get(indefinite);

            if (denominatorExponent == null) {
                // no division necessary for indefinite -> reuse the old entry
                result.put(indefinite, oldPower);
            } else {
                final int denPower = denominatorExponent;
                if (oldPower < denPower) {
                    // indefinite occurs only with an insufficient power in this
                    return null;
                } else if (oldPower > denPower) {
                    result.put(indefinite, oldPower - denPower);
                }
                // else: oldExponent - denPower == 0,
                //       and thus indefinite need not be represented in result
            }
        }
        return new IndefinitePart(result);
    }

    /**
     * @param interpretation maps indefinites to int values they are to be
     * replaced with
     * @param defaultValue value for those indefinites that are not in the
     * keySet of interpretation
     * @return the value this has given interpretation and defaultValue
     */
    public BigInteger interpret(final Map<String, BigInteger> interpretation,
        final BigInteger defaultValue) {
        BigInteger result = BigInteger.ONE; // neutral element of multiplication
        for (final Map.Entry<String, Integer> e : this.exponents.entrySet()) {
            final BigInteger keyInterpretation = interpretation.get(e.getKey());
            final BigInteger keyInter =
                (keyInterpretation == null) ? defaultValue : keyInterpretation;
            final BigInteger keyInterToPower = keyInter.pow(e.getValue());
            result = result.multiply(keyInterToPower);
        }
        return result;
    }

    @Override
    public int hashCode() {
        if (this.hashValid) {
            return this.hashValue;
        }
        this.computeHashValue();
        return this.hashValue;
    }

    private void computeHashValue() {
        this.hashValue = this.exponents.hashCode();
        this.hashValid = true;
    }

    @Override
    public boolean equals(final Object o) {
        IndefinitePart indefinitePart;

        if (!(o instanceof IndefinitePart)) {
            return false;
        }
        indefinitePart = (IndefinitePart) o;

        // profit from our cached hash value
        if (indefinitePart.hashCode() != this.hashCode()) {
            return false;
        }
        return (indefinitePart.exponents.equals(this.exponents));
    }

    /**
     * Compares two IndefiniteParts lexicographically. In ascending order wrt
     * the natural order on Strings, we check which of the two indefinites is
     * the greater one; if they are equal, we check which of the corresponding
     * exponents is bigger; if they are equal as well, we proceed to the next
     * indefinite if existant. In the end, we check whether one of the
     * IndefiniteParts is a proper prefix of the other. If not, they must be
     * equal. E.g.: x*y < x*y*z < x*z < x^2*y
     * @see java.lang.Comparable#compareTo(IndefinitePart)
     * @param other
     * @return
     */
    @Override
    public int compareTo(final IndefinitePart other) {
        SortedMap<String, Integer> m1, m2;
        m1 = new TreeMap<String, Integer>(this.exponents);
        m2 = new TreeMap<String, Integer>(other.exponents);

        Iterator<Map.Entry<String, Integer>> iter1, iter2;
        iter1 = m1.entrySet().iterator();
        iter2 = m2.entrySet().iterator();

        Map.Entry<String, Integer> e1, e2;
        while (iter1.hasNext() && iter2.hasNext()) {
            e1 = iter1.next();
            e2 = iter2.next();

            String key1, key2;
            key1 = e1.getKey();
            key2 = e2.getKey();

            int indefDifference;
            indefDifference = key1.compareTo(key2);
            if (indefDifference < 0) {
                return -1;
            } else if (indefDifference > 0) {
                return 1;
            } else {
                int powerDifference;
                powerDifference = e1.getValue() - e2.getValue();
                if (powerDifference < 0) {
                    return -1;
                } else if (powerDifference > 0) {
                    return 1;
                }
            }
        }

        if (iter1.hasNext()) { // iter2 has not, see loop condition
            return 1;
        } else if (iter2.hasNext()) { // iter1 has not
            return -1;
        } else {
            if (Globals.useAssertions) {
                assert (this.equals(other));
            }
            return 0;
        }
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(final Export_Util eu) {
        if (this.exponents.isEmpty()) {
            return "1";
        }
        final StringBuilder buffer =
            new StringBuilder(5 * this.exponents.size());
        Iterator<Map.Entry<String, Integer>> iter;
        SortedMap<String, Integer> m;
        m = new TreeMap<String, Integer>(this.exponents);
        iter = m.entrySet().iterator();

        while (iter.hasNext()) {
            final Map.Entry<String, Integer> entry = iter.next();
            final String key = entry.getKey();
            final String[] splits = key.split("_", 2);
            buffer.append(splits[0]);
            if (splits.length > 1) {
                buffer.append(eu.sub(splits[1]));
            }
            Integer power;
            power = entry.getValue();
            if (power > 1) {
                buffer.append(eu.sup(power.toString()));
            }
            if (iter.hasNext()) {
                buffer.append(eu.multSign());
            }
        }

        return buffer.toString();
    }

    /**
     * Convert this IndefinitePart to a flat list representation containing the
     * indefinites with their cardinalities.
     * @return A List with the indefinites of this IndefinitePart, regarding
     * cardinality (so x^2 would lead to [x,x])
     */
    public ImmutableList<String> toListRepresentation() {
        final List<String> result = new ArrayList<String>();

        for (final String s : this.exponents.keySet()) {
            for (int i = 1; i <= this.exponents.get(s); i++) {
                result.add(s);
            }
        }

        return ImmutableCreator.create(result);
    }

    /**
     * Like export(Export_Util), but varRepresentations indicates how certain
     * indefinites are supposed to be exported
     * @param eu
     * @param indefRepresentations
     * @return
     */
    public String export(final Export_Util eu,
        final Map<String, String> indefRepresentations) {
        if (this.exponents.isEmpty()) {
            return "1";
        }
        final StringBuilder buffer =
            new StringBuilder(5 * this.exponents.size());
        Iterator<Map.Entry<String, Integer>> iter;
        SortedMap<String, Integer> m;
        m = new TreeMap<String, Integer>(this.exponents);
        iter = m.entrySet().iterator();

        while (iter.hasNext()) {
            final Map.Entry<String, Integer> entry = iter.next();
            final String key = entry.getKey();
            final String indefRep = indefRepresentations.get(key);
            if (indefRep == null) {
                final String[] splits = key.split("_", 2);
                buffer.append(splits[0]);
                if (splits.length > 1) {
                    buffer.append(eu.sub(splits[1]));
                }
            } else {
                buffer.append(indefRep);
            }
            Integer power;
            power = entry.getValue();
            if (power > 1) {
                buffer.append(eu.sup(power.toString()));
            }
            if (iter.hasNext()) {
                buffer.append(eu.multSign());
            }
        }

        return buffer.toString();
    }

    public String toStringRep(final PolyFormatter format) {
        final StringBuilder buffer = new StringBuilder();
        boolean inString = false;

        for (final Map.Entry<String, Integer> e : this.exponents.entrySet()) {
            String var = e.getKey();
            final int power = e.getValue();

            if (inString) {
                buffer.append(format.getMult());
            }
            inString = true;

            var = format.mapVar(var);
            buffer.append(var);
            if (power == 1) {
                continue; // No need to write ^foo
            }

            if (format.getExp() != null) {
                buffer.append(format.getExp());
                buffer.append(power);
            } else { // Emulate exponentiation through multiplication
                for (int i = 1; i < power; i++) {
                    buffer.append(format.getMult());
                    buffer.append(var);
                }
            }
        }

        return buffer.toString();
    }

    /**
     * @return this as a SicstusProlog compatible String
     */
    public String toSicstusProlog() {
        return this.toStringRep(PolyFormatter.PROLOG);
    }

    public String toCiME() {
        return this.toStringRep(PolyFormatter.CIME);
    }

    /**
     * Returns a term representation of this.
     * @param predefined some predefined map
     * @return term
     */
    public TRSTerm toTerm(final IDPPredefinedMap predefined) {
        if (this.equals(IndefinitePart.ONE)) {
            return predefined.getIntTerm(BigIntImmutable.ONE,
                DomainFactory.INTEGERS);
        }

        final FunctionSymbol mulSymbol =
            predefined.getSym(Func.Mul, DomainFactory.INTEGERS);

        TRSTerm result = null;
        for (final Entry<String, Integer> e : this.exponents.entrySet()) {
            if (e.getValue() <= 0) {
                // x^0 = 1 -> no effect in multiplication.
                continue;
            }

            final TRSVariable var = TRSTerm.createVariable(e.getKey());

            // Express x^n by x*x* .. x (n times)
            TRSTerm current = var;
            for (int k = 1; k < e.getValue(); k++) {
                current =
                    TRSTerm.createFunctionApplication(mulSymbol,
                        current, var);
            }

            // The result is the multiplication of all exponents.
            if (result == null) {
                result = current;
            } else {
                result =
                    TRSTerm.createFunctionApplication(mulSymbol,
                        result, current);
            }
        }
        assert result != null : "IndefinitePart is != 1 but also == 1 ?!?";

        return result;
    }

    /**
     * Return a term representation of this. This imlementation uses the default
     * predefined map.
     * @return term
     */
    public TRSTerm toTerm() {
        return this.toTerm(IDPPredefinedMap.DEFAULT_MAP);
    }

    /**
     * @return an SMT-LIB representation of this
     */
    public SMTLIBIntValue toSMTLIB() {
        if (this.exponents.isEmpty()) {
            return SMTLIBIntConstant.create(BigInteger.ONE);
        }

        // seems like there's no exponentiation in the Ints theory,
        // so simulate it by repeated multiplication (here the naive
        // way -- a comb; repeated binary squaring may lead to
        // a more compact representation)
        final List<SMTLIBIntValue> factors = new ArrayList<SMTLIBIntValue>();
        for (final Map.Entry<String, Integer> e : this.exponents.entrySet()) {
            final String var = e.getKey();
            final SMTLIBIntVariable varSmtLib = SMTLIBIntVariable.create(var);
            final int power = e.getValue();
            for (int i = power; i > 0; --i) {
                factors.add(varSmtLib);
            }
        }
        final int size = factors.size();
        if (Globals.useAssertions) {
            assert size > 0;
        }
        final SMTLIBIntValue res = size > 1 ? SMTLIBIntMult.create(factors) : factors.get(0);
        return res;
    }

    void addToDOM(final Element e, final Document doc) {
        for (final Map.Entry<String, Integer> entry : this.exponents.entrySet()) {
            final Element pol = XMLTag.INDEFINIT.createElement(doc);
            final Element var = XMLTag.VARIABLE.createElement(doc);
            final String varName = entry.getKey();
            XMLAttribute.VARNAME.setAttribute(var, varName);
            pol.appendChild(var);

            final Element pow = XMLTag.createInteger(doc, entry.getValue());
            pol.appendChild(pow);

            e.appendChild(pol);
        }
    }

    /**
     * Like <code>addToDOM()</code>, but substitutes the variables contained in
     * <code>varRepresentations</code> by the associated XML subtrees.
     */
    void addToDOM(final Element e,
        final Document doc,
        final Map<String, Element> varRepresentations) {

        for (final Map.Entry<String, Integer> entry : this.exponents.entrySet()) {
            final Element pol = XMLTag.INDEFINIT.createElement(doc);
            final String varName = entry.getKey();
            Element var = varRepresentations.get(varName);
            if (var == null) {
                var = XMLTag.VARIABLE.createElement(doc);
                XMLAttribute.VARNAME.setAttribute(var, varName);
            }
            pol.appendChild(var);

            final Element pow = XMLTag.createInteger(doc, entry.getValue());
            pol.appendChild(pow);

            e.appendChild(pol);
        }
    }

    public IndefinitePart replace(final Map<String, String> renamingMap) {
        final Map<String, Integer> renamed = new HashMap<>();

        for (final Entry<String, Integer> exp : this.getExponents().entrySet()) {
            String var = exp.getKey();

            if (renamingMap.containsKey(var)) {
                var = renamingMap.get(var);
            }
            renamed.put(var, exp.getValue());
        }
        return IndefinitePart.create(renamed);
    }

    public BigInteger tryEvaluate(final Map<String, BigInteger> valueMap) {
        BigInteger result = BigInteger.ONE;

        for (final Entry<String, Integer> exp : this.getExponents().entrySet()) {
            final String var = exp.getKey();

            if (valueMap.containsKey(var)) {
                result = result.multiply(valueMap.get(var).pow(exp.getValue()));
            } else {
                return null;
            }
        }
        return result;
    }

    public MinMaxExpr toMinMaxPoly() {
        MinMaxExpr one = MinMaxExpr.createInt(BigInteger.ONE);
        if (exponents.isEmpty()) {
            return one;
        }
        Iterator<Entry<String, Integer>> it = exponents.entrySet().iterator();
        Entry<String, Integer> e = it.next();
        String varname = e.getKey();
        int exponent = e.getValue();
        MinMaxExpr res;
        if (exponent == 0) {
            res = one;
        } else {
            MinMaxExpr var = MinMaxExpr.createVar(varname);
            res = var;
            for (int i = 1; i < exponent; i++) {
                res = MinMaxExpr.createTimes(res, var);
            }
        }
        while (it.hasNext()) {
            e = it.next();
            varname = e.getKey();
            exponent = e.getValue();
            MinMaxExpr m;
            if (exponent > 0) {
                MinMaxExpr var = MinMaxExpr.createVar(varname);
                m = var;
                for (int i = 1; i < exponent; i++) {
                    m = MinMaxExpr.createTimes(m, var);
                }
                res = MinMaxExpr.createTimes(res, m);
            }
        }
        return res;
    }

    /**
     * converts a coeffient * this indefinite part into CPF-LTS format
     * @param coeff the coefficient
     * @param vars a mapping from indefinite part variables to CPF variables
     */
    public Element toCpfLTS(Document doc, Element coeff, Map<String, String> vars) {
	if (this.getExponents().size() == 0) {
            return coeff;
        } else {
            final Element product = CPFTag.PRODUCT.create(doc, coeff);
            for (final Map.Entry<String, Integer> factor : this.getExponents().entrySet()) {
                final String xName = factor.getKey();
                for (int i = 0; i < factor.getValue(); i++) {
                    String x = vars.get(xName);
                    if (x == null) {
                		throw new RuntimeException("problem in vars-map for " + xName + " and " + vars);
                    }
                    product.appendChild(
                        CPFTag.LTS_VARIABLE_ID.create(doc, x));
                }
            }
            return product;
        }
    }

}
