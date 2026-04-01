package aprove.verification.oldframework.Algebra.Polynomials;

import static aprove.verification.oldframework.Algebra.Polynomials.ConstraintType.*;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Carsten Fuhs
 * @version $Id$
 *
 * A SimplePolynomial is a polynomial whose coefficients are integer numbers.
 * It is supposed to represent the (parametric) coefficient of a polynomial
 * with proper variables (i.e., a VarPolynomial). Here variables of a
 * SimplePolynomial are meant to be instantiated by non-negative numbers only.
 *
 * Addends which amount to zero are not represented explicitly (of which all
 * methods which generate SimplePolynomials must take care). Addition and
 * multiplication are the standard operations. This class is also often used in
 * representations for polynomial constraints where a satisfying assignment of
 * variables to natural numbers is desired.
 *
 * As a design decision, variables are represented by Strings. Moreover,
 * polynomials are always represented as sums of products of a coefficient
 * and variables. Thus, (4*a+b)*(c+d)*(e+f) will be represented as
 * 4*a*c*e + 4*a*c*f + 4*a*d*e + 4*a*d*f + b*c*e + b*c*f + b*d*e + b*d*f.
 *
 * Advantage: Every polynomial has a unique representation, so
 * SimplePolynomial.equals() does what one would expect and does it efficiently.
 * Disadvantage: This representation may require exponentially more space than
 * allowing arbitrary combinations of sums and products. This can (obviously) be
 * quite inconvenient, e.g., for use in matrix interpretations.
 *
 * However, there exist algorithms (like FDSearch, our implementation of
 * Contejean's algorithm) which require their input to be a sum of monomials
 * (i.e., products of variables and numbers).
 *
 * Note for the interface Comparable: SimplePolynomial.compareTo conducts a
 * comparison on /syntactic/ level, not on arithmetic level (otherwise,
 * "a" and "b" would be incomparable, which would violate the contract of
 * Comparable.
 */
public class SimplePolynomial
implements
Immutable,
Exportable,
Comparable<SimplePolynomial>,
XMLObligationExportable
{
    // map the product of indefinite coefficients of each monomial over such
    // coefficients (a_i) to its numerical coefficient; each entry is an
    // addend of the monomial (an example for the "additive" normal form the
    // poly is in: 3*(a_1^2*a_2^7) + (-7)*(a_3^3) + 3*(IndefinitePart.ONE))
    private final ImmutableMap<IndefinitePart, BigInteger> simpleMonomials;

    private int hashValue; // cache for the hash value
    private boolean hashValid; // has the hash value already been computed?

    /* The following constants are by no means unique, so comparing to them
     * via "==" is dangerous; rather use equals().
     */
    public static final SimplePolynomial MINUS_ONE = new SimplePolynomial(-1); // -1
    public static final SimplePolynomial ZERO = new SimplePolynomial(0); // 0
    public static final SimplePolynomial ONE = new SimplePolynomial(1); // 1

    /**
     * Creates a new SimplePolynomial with simpleMonomials as product of
     * indefinite coefficients-to-numerical factor mapping. Each entry of
     * simpleMonomials corresponds to an addend of this. Uses the empty mapping
     * in case simpleMonomials == null. simpleMonomials will not be modified by
     * this class, and it must not be modified outside of this class either. In
     * case modifications are desired, pass a copy to the constructor.
     * @param simpleMonomials the mapping from IndefiniteParts to numerical
     * factors which is to be integrated in this
     */
    private SimplePolynomial(final Map<IndefinitePart, BigInteger> simpleMonomials) {
        if (simpleMonomials == null) {
            this.simpleMonomials = ImmutableCreator.create(Collections.<IndefinitePart, BigInteger>emptyMap());
        } else {
            if (Globals.useAssertions) {
                assert (!simpleMonomials.values().contains(BigInteger.ZERO));
            }
            this.simpleMonomials = ImmutableCreator.create(simpleMonomials);
        }
        this.hashValid = false;
    }

    /**
     * Creates a new SimpleMonomial which is equivalent to constant.
     * @param constant the constant to which this is to be equivalent
     */
    private SimplePolynomial(final int constant) {
        if (constant == 0) {
            final Map<IndefinitePart, BigInteger> simpleMonomials = Collections.<IndefinitePart, BigInteger>emptyMap();
            this.simpleMonomials = ImmutableCreator.create(simpleMonomials);
        } else {
            final Map<IndefinitePart, BigInteger> simpleMonomials =
                Collections.<IndefinitePart, BigInteger>singletonMap(IndefinitePart.ONE, BigInteger.valueOf(constant));
            this.simpleMonomials = ImmutableCreator.create(simpleMonomials);
        }
        this.hashValid = false;
    }

    /**
     * Creates a new SimpleMonomial which is equivalent to constant.
     * @param constant the constant to which this is to be equivalent
     */
    private SimplePolynomial(final BigInteger constant) {
        if (constant == null || constant.signum() == 0) {
            final Map<IndefinitePart, BigInteger> simpleMonomials = Collections.<IndefinitePart, BigInteger>emptyMap();
            this.simpleMonomials = ImmutableCreator.create(simpleMonomials);
        } else {
            Map<IndefinitePart, BigInteger> simpleMonomials;
            simpleMonomials = Collections.<IndefinitePart, BigInteger>singletonMap(IndefinitePart.ONE, constant);
            this.simpleMonomials = ImmutableCreator.create(simpleMonomials);
        }
        this.hashValid = false;
    }

    /**
     * Creates a new SimpleMonomial which is equivalent to indefinite.
     * @param indefinite the indefinite of which this is supposed to consist
     */
    private SimplePolynomial(final String indefinite) {
        final Map<String, Integer> exponents = Collections.singletonMap(indefinite, 1);
        final IndefinitePart indefinitePart = new IndefinitePart(exponents);
        final Map<IndefinitePart, BigInteger> simpleMonomials =
            Collections.singletonMap(indefinitePart, BigInteger.ONE);
        this.simpleMonomials = ImmutableCreator.create(simpleMonomials);
        this.hashValid = false;
    }

    /**
     * @param simpleMonomials - non-null mapping of IndefiniteParts to their
     * factors; MUST NOT be modified after calling this method. if this is
     * desired, pass a copy instead.
     * @return a corresponding SimplePolynomial
     */
    public static SimplePolynomial create(final Map<IndefinitePart, BigInteger> simpleMonomials) {
        return new SimplePolynomial(simpleMonomials);
    }

    public static SimplePolynomial create(final String a) {
        return new SimplePolynomial(a);
    }

    public static SimplePolynomial create(final BigInteger constant) {
        return new SimplePolynomial(constant);
    }

    public static SimplePolynomial create(final int constant) {
        switch (constant) {
        case 0:
            return SimplePolynomial.ZERO;
        case 1:
            return SimplePolynomial.ONE;
        case -1:
            return SimplePolynomial.MINUS_ONE;
        default:
            return new SimplePolynomial(constant);
        }
    }

    public static SimplePolynomial create(final IndefinitePart iPart, final BigInteger factor) {
        if (Globals.useAssertions) {
            assert iPart != null;
        }
        return new SimplePolynomial(Collections.singletonMap(iPart, factor));
    }

    /**
     * Converts a Polynomial without variables (only indefinite coefficients and
     * numerical coefficients) to an equivalent SimplePolynomial.
     * @param poly the Polynomial to be converted to a SimplePolynomial; assumed
     * not to contain any variables.
     * @return the resulting SimplePolynomial, or null if poly == null
     */
    public static SimplePolynomial toSimplePolynomial(final Polynomial poly) {

        if (poly == null) {
            return null;
        }
        SimplePolynomial result = SimplePolynomial.ZERO; // to be returned
        IndefinitePart currentIndefinitePart;
        // temporary variable for the IndefinitePart implicitly
        // contained in the monomial

        for (final Monomial monomial : poly) {
            if (monomial.exponents == null || monomial.exponents.isEmpty()) {
                // only a fixed (integer) number in the Monomial,
                // no indefinite coefficients
                result = result.plus(IndefinitePart.ONE, BigInteger.valueOf(monomial.coeff));
            } else {
                currentIndefinitePart = new IndefinitePart(new LinkedHashMap<String, Integer>(monomial.exponents));
                result = result.plus(currentIndefinitePart, BigInteger.valueOf(monomial.coeff));
            }
        }

        return result;
    }

    /**
     * Converts a SimplePolynomial to an equivalent Polynomial.
     * @param simplePoly the SimplePolynomial to be converted
     * @return a Polynomial equivalent to simplePoly
     */
    @Deprecated
    public static Polynomial toPolynomial(final SimplePolynomial simplePoly) {

        if (simplePoly == null) {
            return null;
        }
        Polynomial result = Polynomial.createConstant(0); // to be returned
        Polynomial newPoly; // temporary variable, needed for being able to
        // use Polynomial's plus method

        for (final Map.Entry<IndefinitePart, BigInteger> entry : simplePoly.simpleMonomials.entrySet()) {
            if (!BigInteger.valueOf(entry.getValue().intValue()).equals(entry.getValue())) {
                return null; // Polynomial cannot cope with int overflows.
            }
            newPoly = Polynomial.createConstant(0);
            newPoly.add(Monomial.create(entry.getValue().intValue(), new TreeMap<String, Integer>(entry
                .getKey()
                .getExponents())));
            result = result.plus(newPoly);
        }

        return result;
    }

    /**
     * Adds a SimplePolynomial to this. The result is optimized, i.e., no
     * products with 0 as one of the factors remain represented explicitly.
     * @param simplePoly the addend
     * @return the sum of the two polynomials
     */
    public SimplePolynomial plus(final SimplePolynomial simplePoly) {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        // to be returned as SimplePolynomial

        BigInteger sum; // temporary variable for a sum of factors

        // First consider all Map Entries that occur in this ...
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey();
            final BigInteger value = entry.getValue();
            final BigInteger simplePolyValue = simplePoly.simpleMonomials.get(key);
            if (simplePolyValue == null) {
                result.put(key, value);
            } else {
                sum = value.add(simplePolyValue);
                if (sum.signum() != 0) {
                    result.put(key, sum);
                }
            }
        }

        // ... then include the mappings of the keys that occur only in simplePoly as well.
        for (final Map.Entry<IndefinitePart, BigInteger> entry : simplePoly.simpleMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey();
            final BigInteger value = entry.getValue();

            if (!this.simpleMonomials.containsKey(key)) {
                result.put(key, value);
            }
        }

        return new SimplePolynomial(result);
    }

    /**
     * Adds a single "simpleMonomial", that is, a pair (IndefinitePart, factor)
     * to this. Used by toSimplePolynomial(Polynomial).
     * @param key the IndefinitePart of the "simpleMonomial" to be added
     * @param value the corresponding factor of the "simpleMonomial" to be added
     * @return the sum of this and the pair (key, value)
     */
    private SimplePolynomial plus(final IndefinitePart key, final BigInteger value) {
        Map<IndefinitePart, BigInteger> result;
        // to be returned (as the corresponding SimplePolynomial)

        BigInteger sum; // temporary variable for a sum of factors
        BigInteger factor; // stores the factor to which key is mapped by this

        result = new LinkedHashMap<IndefinitePart, BigInteger>(this.simpleMonomials);

        factor = this.simpleMonomials.get(key);

        if (factor != null) {
            sum = factor.add(value);
            if (sum.signum() != 0) {
                result.put(key, sum);
            } else { // key |-> 0  is redundant.
                result.remove(key);
            }
        } else { // key not contained by this
            result.put(key, value);
        }

        return SimplePolynomial.create(result);

    }

    public static SimplePolynomial plus(final Collection<SimplePolynomial> values) {
        Map<IndefinitePart, BigInteger> result;
        // to be returned (as the corresponding SimplePolynomial)
        result = new LinkedHashMap<IndefinitePart, BigInteger>();

        for (final SimplePolynomial poly : values) {
            for (final Map.Entry<IndefinitePart, BigInteger> entry : poly.simpleMonomials.entrySet()) {
                final IndefinitePart key = entry.getKey();
                final BigInteger resultValue = result.get(key);
                if (resultValue != null) {
                    final BigInteger newValue = resultValue.add(entry.getValue());
                    if (newValue.signum() == 0) {
                        result.remove(key);
                    } else {
                        result.put(key, newValue);
                    }
                } else {
                    result.put(key, entry.getValue());
                }
            }
        }

        return SimplePolynomial.create(result);

    }

    /**
     * This method tries to compute the product of a collection of SPs without
     * using too many deep copies. It succeeds in doing so if all factors
     * consist of only one monomial, otherwise it falls back to multiplication
     * one-by-one.
     * @param values
     * @return
     */
    public static SimplePolynomial times(final Collection<SimplePolynomial> values) {
        Map<IndefinitePart, BigInteger> result;
        // to be returned (as the corresponding SimplePolynomial)
        result = new LinkedHashMap<IndefinitePart, BigInteger>();

        final List<IndefinitePart> keys = new ArrayList<IndefinitePart>();
        BigInteger resInt = BigInteger.ONE;
        boolean useOneByOne = false;

        // First check if applicable...
        for (final SimplePolynomial poly : values) {
            if (poly.simpleMonomials.size() > 1) {
                // Have to do the old way.
                useOneByOne = true;
                break;
            }
            for (final Map.Entry<IndefinitePart, BigInteger> entry : poly.simpleMonomials.entrySet()) {
                // There is only one. We know that.
                final IndefinitePart key = entry.getKey();
                keys.add(key);
                resInt = resInt.multiply(entry.getValue());

            }
        }
        if (!useOneByOne) {
            result.put(IndefinitePart.times(keys), resInt);
            return SimplePolynomial.create(result);
        } else {
            // We have to do this one by one.
            SimplePolynomial tmp = SimplePolynomial.ONE;
            for (final SimplePolynomial poly : values) {
                tmp = tmp.times(poly);
            }
            return tmp;
        }

    }

    /**
     * Gets the factor that corresponds to indefinitePart inside this.
     * @param indefinitePart the IndefinitePart whose factor is to be computed
     * @return the factor with which indefinitePart occurs in this (0 if it
     * doesn't)
     */
    BigInteger getFactor(final IndefinitePart indefinitePart) {
        BigInteger result;

        result = this.simpleMonomials.get(indefinitePart);

        if (result == null) { // indefinitePart does not occur in this,
            return BigInteger.ZERO; // i.e., it occurs with factor 0
        } else {
            return result;
        }
    }

    public SimplePolynomial times(final BigInteger factor) {
        if (factor.signum() == 0) {
            return SimplePolynomial.ZERO;
        }
        final Map<IndefinitePart, BigInteger> result =
            new LinkedHashMap<IndefinitePart, BigInteger>(this.simpleMonomials.size());
        for (final Entry<IndefinitePart, BigInteger> monomial : this.simpleMonomials.entrySet()) {
            final BigInteger newCoeff = monomial.getValue().multiply(factor);
            result.put(monomial.getKey(), newCoeff);
        }
        return SimplePolynomial.create(result);
    }

    /**
     * Multiplies an indefinitePart to this.
     */
    public SimplePolynomial times(final IndefinitePart indef) {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        // to be returned (as the corresponding SimplePolynomial)

        IndefinitePart newKey; // temporary variable for a product of
        // IndefiniteParts

        for (final Map.Entry<IndefinitePart, BigInteger> entry1 : this.simpleMonomials.entrySet()) {
            final IndefinitePart key1 = entry1.getKey();
            newKey = key1.times(indef);
            result.put(newKey, entry1.getValue());
        }

        return SimplePolynomial.create(result);
    }

    /**
     * Multiplies a SimplePolynomial to this.
     * @param simplePoly the simplePolynomial to be multiplied to this
     * @return the product of this and simplePoly
     */
    // TODO: use abortable function in more methods
    public SimplePolynomial times(final SimplePolynomial simplePoly) {
        SimplePolynomial result = null;
        try {
            result = this.times(simplePoly, AbortionFactory.create());
        } catch (final AbortionException e) {
            throw new RuntimeException(e);
        }
        return result;
    }

    public SimplePolynomial times(final SimplePolynomial simplePoly, final Abortion aborter) throws AbortionException {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        // to be returned (as the corresponding SimplePolynomial)

        IndefinitePart newKey; // temporary variable for a product of
        // IndefiniteParts
        BigInteger newValue; // temporary variable for a product of factors

        aborter.checkAbortion();
        for (final Map.Entry<IndefinitePart, BigInteger> entry1 : this.simpleMonomials.entrySet()) {
            final IndefinitePart key1 = entry1.getKey();
            final BigInteger value1 = entry1.getValue();

            for (final Map.Entry<IndefinitePart, BigInteger> entry2 : simplePoly.simpleMonomials.entrySet()) {
                aborter.checkAbortion();
                newKey = key1.times(entry2.getKey());
                newValue = value1.multiply(entry2.getValue());
                final BigInteger oldValue = result.get(newKey);
                if (oldValue == null) {
                    result.put(newKey, newValue);
                } else {
                    newValue = newValue.add(oldValue);
                    if (newValue.signum() == 0) {
                        result.remove(newKey);
                    } else {
                        result.put(newKey, newValue);
                    }
                }
            }
        }

        return SimplePolynomial.create(result);
    }

    /**
     * Returns this<sup>exponent</sup>.
     * @param exponent non-negative exponent
     * @return this<sup>exponent</sup>
     */
    public SimplePolynomial power(int exponent) {
        if (Globals.useAssertions) {
            assert (exponent >= 0);
        }
        if (exponent == 0) {
            return SimplePolynomial.ONE;
        } else if (exponent == 1) {
            return this;
        } else {
            SimplePolynomial result = SimplePolynomial.ONE;
            SimplePolynomial tmp = this;
            while (exponent > 0) {
                if (exponent % 2 == 1) {
                    result = result.times(tmp);
                }
                exponent /= 2;
                if (exponent > 0) {
                    tmp = tmp.times(tmp);
                } else {
                    break; // somewhat ugly, but slightly more efficient
                    // (saves the last check of the loop cond.)
                }
            }
            return result;
        }
    }

    /**
     * @return a negated version of this
     */
    public SimplePolynomial negate() {
        final Map<IndefinitePart, BigInteger> result =
            new LinkedHashMap<IndefinitePart, BigInteger>(this.simpleMonomials.size());
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            result.put(entry.getKey(), entry.getValue().negate());
        }
        return SimplePolynomial.create(result);
    }

    /**
     * @param subtrahend to be subtracted from this
     * @return this - subtrahend
     */
    public SimplePolynomial minus(final SimplePolynomial subtrahend) {
        final Map<IndefinitePart, BigInteger> result =
            new LinkedHashMap<IndefinitePart, BigInteger>(this.simpleMonomials.size()
                + subtrahend.simpleMonomials.size());
        // to be returned as SimplePolynomial

        BigInteger difference; // temporary variable for a difference of factors

        // First consider all Map Entries that occur in this ...
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey();
            final BigInteger value = entry.getValue();

            final BigInteger simplePolyValue = subtrahend.simpleMonomials.get(key);
            if (simplePolyValue == null) {
                result.put(key, value);
            } else {
                difference = value.subtract(simplePolyValue);
                if (difference.signum() != 0) {
                    result.put(key, difference);
                }
            }
        }

        // ... then include the mappings of the keys that occur only in subtrahend as well.
        for (final Map.Entry<IndefinitePart, BigInteger> entry : subtrahend.simpleMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey();
            final BigInteger value = entry.getValue();

            if (!this.simpleMonomials.containsKey(key)) {
                result.put(key, value.negate());
            }
        }

        return SimplePolynomial.create(result);
    }

    /**
     * @param value to be assigned to each indefinite in this
     * @return the SimplePolynomial in which all indefinites are assigned the
     * number <code>value</code>.
     */
    public SimplePolynomial setAllIndefinitesTo(final BigInteger value) {
        Map<IndefinitePart, BigInteger> polyMap;
        BigInteger factor = BigInteger.ZERO; // will be multiplied to IndefinitePart.ONE

        for (final Map.Entry<IndefinitePart, BigInteger> e : this.simpleMonomials.entrySet()) {
            final BigInteger currentValue = e.getValue();
            BigInteger intermediateResult;
            intermediateResult = e.getKey().setAllIndefinitesTo(value);
            factor = factor.add(intermediateResult.multiply(currentValue));
        }
        if (factor.signum() == 0) {
            return SimplePolynomial.ZERO;
        }
        polyMap = Collections.<IndefinitePart, BigInteger>singletonMap(IndefinitePart.ONE, factor);
        return SimplePolynomial.create(polyMap);
    }

    /**
     * Computes a version of this in which the coefficients of this that occur
     * in the key set of values are replaced by the corresponding numerical
     * values indicated by values.
     * @param values coefficient-to-value mapping for known coefficient values
     * @return the specialized SimplePolynomial
     */
    public SimplePolynomial specialize(final Map<String, BigInteger> values) {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            BigInteger currentValue = entry.getValue();
            final Pair<IndefinitePart, BigInteger> intermediateResult = entry.getKey().specialize(values);
            if (intermediateResult.y.signum() != 0) { // no need to add 0 * some IndefinitePart
                currentValue = currentValue.multiply(intermediateResult.y);
                final BigInteger oldValue = result.get(intermediateResult.x);
                if (oldValue == null) { // intermediateResult.x not yet in result
                    result.put(intermediateResult.x, currentValue);
                } else {
                    final BigInteger newValue = oldValue.add(currentValue);
                    if (newValue.signum() == 0) {
                        result.remove(intermediateResult.x);
                    } else {
                        result.put(intermediateResult.x, newValue);
                    }
                }
            }
        }
        return SimplePolynomial.create(result);
    }

    /**
     * Computes a version of this in which the coefficients of this that occur
     * in the key set of values are replaced by the corresponding numerical
     * values or indefinite coefficients indicated by values.
     * @param values coefficient-to-number/coefficient mapping
     * @return the specialized SimplePolynomial
     */
    public SimplePolynomial specializeGENode(final Map<String, GENode> values) {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            BigInteger currentValue = entry.getValue();
            final Pair<IndefinitePart, BigInteger> intermediateResult = entry.getKey().specializeGENode(values);
            if (intermediateResult.y.signum() != 0) { // no need to add 0 * some IndefinitePart
                currentValue = currentValue.multiply(intermediateResult.y);
                final BigInteger oldValue = result.get(intermediateResult.x);
                if (oldValue == null) { // intermediateResult.x not yet in result
                    result.put(intermediateResult.x, currentValue);
                } else {
                    final BigInteger newValue = oldValue.add(currentValue);
                    if (newValue.signum() == 0) {
                        result.remove(intermediateResult.x);
                    } else {
                        result.put(intermediateResult.x, newValue);
                    }
                }
            }
        }
        return SimplePolynomial.create(result);
    }

    /**
     * @return whether this represents 0
     */
    public boolean isZero() {
        return this.simpleMonomials.isEmpty();
    }

    /**
     * @param forbiddenIndefinites the indefinites that are to be eliminiated
     * from this
     * @return the SimplePolynomial that results from (de facto) substituting
     * each element of forbiddenIndefinites by 1 in this
     */
    SimplePolynomial removeIndefinites(final Set<String> forbiddenIndefinites) {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart oldIndefinitePart = entry.getKey();
            final IndefinitePart newIndefinitePart = oldIndefinitePart.removeIndefinites(forbiddenIndefinites);
            final BigInteger factor = result.get(newIndefinitePart);
            if (factor == null) {
                // newIndefinitePart does not occur in result yet,
                // just include it with the same factor as before
                result.put(newIndefinitePart, entry.getValue());
            } else {
                // newIndefinitePart already present in result
                final BigInteger newFactor = factor.add(entry.getValue());
                if (newFactor.signum() == 0) {
                    result.remove(newIndefinitePart);
                } else {
                    result.put(newIndefinitePart, newFactor);
                }
            }
        }
        return SimplePolynomial.create(result);
    }

    /**
     * Returns a version of this in which forbiddenIndefinites are replaced by
     * 1. Note that this method is only to be called if the result of
     * substituting forbiddenIndefinites by 1 will have as many addends as this,
     * otherwise the result will probably be semantically incorrect. (a1*a2 +
     * a1*a2^2 should become 2*a1 and not a1 as returned by this method when
     * called with a2 as parameter.) Always safe to call if this only has one
     * addend. In case of more addends, it is probably a better idea to use
     * removeIndefinites(...), which should work for arbitrary numbers of
     * addends in this, but works less efficiently.
     * @param forbiddenIndefinite the indefinite to be removed from the
     * addend(s) of this
     * @return the SimplePolynomial that results from omitting
     * forbiddenIndefinites in this
     */
    SimplePolynomial removeIndefinitesEfficiently(final Set<String> forbiddenIndefinites) {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart oldIndefinitePart = entry.getKey();

            IndefinitePart newIndefinitePart;

            newIndefinitePart = oldIndefinitePart.removeIndefinites(forbiddenIndefinites);
            result.put(newIndefinitePart, entry.getValue());
            // just include the result of the removal in result without
            // checking whether the IndefinitePart is already known there
        }
        return SimplePolynomial.create(result);
    }

    /**
     * Apply substitution to this. Note that only real variables are
     * substituted, not indefinite coefficients.
     * @param substitution to be performed on this
     * @return substituted this
     */
    public SimplePolynomial substitute(final Map<String, SimplePolynomial> substitution) {
        SimplePolynomial result = null;
        try {
            result = this.substitute(substitution, AbortionFactory.create());
        } catch (final AbortionException e) {
            throw new RuntimeException(e);
        }
        return result;
    }

    public SimplePolynomial substitute(final Map<String, SimplePolynomial> substitution, final Abortion aborter)
        throws AbortionException
        {
        SimplePolynomial result = SimplePolynomial.ZERO;

        // iterate over all indefinite parts of this polynomial
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart keyIP = entry.getKey();
            SimplePolynomial substitutePoly = SimplePolynomial.ONE;
            final Set<String> substitutedVars = new LinkedHashSet<String>();

            // iterate over variables of the substitution set
            for (final Map.Entry<String, SimplePolynomial> substEntry : substitution.entrySet()) {
                final String substKey = substEntry.getKey();

                /* multiply the resulting polys at the power at which their
                   key used to occur in keyIP (if > 0)
                   and remember the key to remove it later */
                final int exponent = keyIP.getExponent(substKey);
                if (exponent > 0) {
                    substitutePoly = substitutePoly.times(substEntry.getValue().power(exponent), aborter);
                    substitutedVars.add(substKey);
                }
            }

            // remove substituted vars from keyIP
            final IndefinitePart newIP = keyIP.removeIndefinites(substitutedVars);

            // multiply the resulting poly to newIP*entry.getValue()
            final Map<IndefinitePart, BigInteger> newMonomial = new LinkedHashMap<IndefinitePart, BigInteger>();
            newMonomial.put(newIP, entry.getValue());
            substitutePoly = substitutePoly.times(new SimplePolynomial(newMonomial), aborter);

            // add substitutePoly to result
            result = result.plus(substitutePoly);
        }

        return result;
        }

    /**
     * For all addends of this which can be divided by substituteMe, replace
     * substituteMe by number to the highest degree possible, e.g. for this == 3
     * * a1^3 * a2^2 * a3, substituteMe == a1 * a2 and number == 4, the result
     * will be 48 * a1 * a3.
     * @param substituteMe the IndefinitePart by which we have to try to divide
     * the addends
     * @param number the number with which we multiply the addends in case of
     * successful division
     * @return the resulting SimplePolynomial
     */
    SimplePolynomial substitute(final IndefinitePart substituteMe, final BigInteger number) {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {

            // the IndefinitePart in which the substitution is taking place
            final IndefinitePart oldIndefinitePart = entry.getKey();

            // the new factor for the resulting IndefinitePart
            BigInteger newFactor = entry.getValue();

            // store the result of the last successful division
            IndefinitePart newIndefinitePart = oldIndefinitePart;

            // store the result of the last division attempt
            IndefinitePart divisionResult = newIndefinitePart.divide(substituteMe);

            // iterate the division as long as possible
            while (divisionResult != null) {
                newFactor = newFactor.multiply(number);
                newIndefinitePart = divisionResult;
                divisionResult = newIndefinitePart.divide(substituteMe);
            }

            // take care, the resulting IndefinitePart may already be part
            // of our result

            // the factor with which newIndefinitePart occurs in result so far
            final BigInteger factorSoFar = result.get(newIndefinitePart);

            if (factorSoFar == null) {
                result.put(newIndefinitePart, newFactor);
            } else {
                final BigInteger resultingFactor = newFactor.add(factorSoFar);
                if (resultingFactor.signum() != 0) {
                    result.put(newIndefinitePart, resultingFactor);
                } else {
                    result.remove(newIndefinitePart);
                }
            }
        }
        return SimplePolynomial.create(result);
    }

    /**
     * @return a Set of all indefinites (variables/coefficients) that occur in
     * this.
     */
    public Set<String> getIndefinites() {
        final Set<String> result = new LinkedHashSet<String>();
        for (final IndefinitePart key : this.simpleMonomials.keySet()) {
            result.addAll(key.getIndefinites());
        }
        return result;
    }

    /**
     * @return a Set of all IndefiniteParts that occur in this.
     */
    public Set<IndefinitePart> getIndefiniteParts() {
        return new LinkedHashSet<IndefinitePart>(this.simpleMonomials.keySet());
    }

    /**
     * @return whether all addends of this have numerical coefficients > 0 (true
     * in case of the empty SimplePolynomial, which is equal to 0)
     */
    public boolean allPositive() {
        for (final BigInteger value : this.simpleMonomials.values()) {
            if (value.signum() <= 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return whether all addends of this have numerical coefficients < 0 (true
     * in case of the empty SimplePolynomial, which is equal to 0)
     */
    public boolean allNegative() {
        for (final BigInteger value : this.simpleMonomials.values()) {
            if (value.signum() >= 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * Get the numerical addend of this.
     * @return the numerical addend of this.
     */
    public BigInteger getNumericalAddend() {
        final BigInteger result = this.simpleMonomials.get(IndefinitePart.ONE);
        if (result == null) {
            return BigInteger.ZERO;
        }
        return result;
    }

    /**
     * @return If this has the form a_i - a_j, a_i - n or a_i for some
     * indefinites a_i, a_j and some number n, <a_i, a_j>, <a_i, n> or <a_i, 0>,
     * respectively, is returned. Otherwise, null is returned.
     */
    public Pair<GENode, GENode> toGENodePair() {
        GENode node1 = null; // 1st component of result
        GENode node2 = null; // 2nd component of result
        switch (this.numberOfAddends()) {
        case 1: {
            // check whether this consists of a single indefinite,
            // regardless of its power
            final Set<String> indefinites = this.simpleMonomials.keySet().iterator().next().getIndefinites();
            if (indefinites.size() != 1) {
                return null;
            } else {
                node1 = GENode.create(indefinites.iterator().next());
                node2 = GENode.create(BigInteger.ZERO);
            }
            break;
        }
        case 2: {
            // here, we'd like this to be of the form a_i - a_j or a_i - n
            // (actually, we hope; otherwise return null)
            // hence: get the IndefiniteParts and analyze them
            final Iterator<Map.Entry<IndefinitePart, BigInteger>> entryIter =
                this.simpleMonomials.entrySet().iterator();

            // take care of the 1st addend ...
            final Map.Entry<IndefinitePart, BigInteger> addend1 = entryIter.next();
            final Pair<GENode, GENode> pair1 = this.addendToPair(addend1);
            if (pair1 == null) {
                return null;
            } else {
                node1 = pair1.x;
                node2 = pair1.y;
            }

            // ... then of the 2nd addend
            final Map.Entry<IndefinitePart, BigInteger> addend2 = entryIter.next();
            final Pair<GENode, GENode> pair2 = this.addendToPair(addend2);
            if (pair2 == null) {
                return null;
            } else if (pair2.x != null) {
                node1 = pair2.x;
            } else {
                if (Globals.useAssertions) {
                    assert (pair2.y != null);
                } // pair2 contains s.th., but not in its 1st component

                node2 = pair2.y;
            }
            break;
        }
        default: // unsuitable number of addends (zero addends don't help either)
            return null;
        }

        // check whether we have a decent result
        if ((node1 != null) && (node2 != null)) {
            return new Pair<GENode, GENode>(node1, node2);
        } else {
            return null;
        }
    }

    /**
     * Given one of (supposedly) two addends (simple monomials), check whether
     * the addend matches (1) a_i (2) - a_i or (3) n (n being an Integer) and
     * return a suitable Pair (1) <a_i, null> (2) <null, a_i> (3) <null, - n>
     * @param addend a map entry in which an IndefinitePart is mapped to its
     * factor; the factor must be smaller than maxint
     * @return the corresponding Pair of GENodes if addend matches one of the
     * cases (1), (2) or (3); null otherwise
     */
    private Pair<GENode, GENode> addendToPair(final Map.Entry<IndefinitePart, BigInteger> addend) {
        GENode node1 = null; // 1st component of result
        GENode node2 = null; // 2nd component of result
        final IndefinitePart iPart = addend.getKey();
        final int numberOfIndefinites = iPart.numberOfIndefinites();
        switch (numberOfIndefinites) {
        case 0:
            // found n
            node2 = GENode.create(addend.getValue().negate());
            break;
        case 1:
            final BigInteger factor = addend.getValue();
            if (factor.equals(BigInteger.ONE) || factor.equals(BigInteger.valueOf(-1))) {
                final String indefinite = iPart.toIndefinite();
                if (indefinite == null) {
                    // iPart has an exponent != 1.
                    return null;
                } else if (factor.equals(BigInteger.ONE)) {
                    node1 = GENode.create(indefinite);
                } else { // factor == -1
                    node2 = GENode.create(indefinite);
                }
            } else { // unsuitable factor
                return null;
            }
            break;
        default:
            // more than one indefinite
            return null;
        }
        return new Pair<GENode, GENode>(node1, node2);
    }

    /**
     * @return If this has the form a_i - a_j, a_i - n or a_i for some
     * indefinites a_i, a_j and some number n, <a_i, a_j>, <a_i, n> or <a_i, 0>,
     * respectively, is returned. Otherwise, null is returned. as opposed to
     * "toGeNodePair", we only consider a^k = 0 for odd values of k (since here
     * we consider indefinites to range over integers, which is different for
     * most other methods of this class, where only the naturals are considered)
     */
    public Pair<GENode, GENode> toGENodePairForSearchBounds() {
        GENode node1 = null; // 1st component of result
        GENode node2 = null; // 2nd component of result
        switch (this.numberOfAddends()) {
        case 1: {
            // check whether this consists of a single indefinite at an odd power
            final Set<String> indefinites = this.simpleMonomials.keySet().iterator().next().getIndefinites();
            if (indefinites.size() != 1) {
                return null;
            } else {
                final String var = indefinites.iterator().next();
                final Set<Entry<IndefinitePart, BigInteger>> monomials = this.simpleMonomials.entrySet();
                for (final Entry<IndefinitePart, BigInteger> e : monomials) {
                    final IndefinitePart iPart = e.getKey();
                    final int exp = iPart.getExponent(var);
                    if (exp % 2 != 1) {
                        return null;
                    }
                }

                node1 = GENode.create(var);
                node2 = GENode.create(BigInteger.ZERO);
            }
            break;
        }
        case 2: {
            // here, we'd like this to be of the form a_i - a_j or a_i - n
            // (actually, we hope; otherwise return null)
            // hence: get the IndefiniteParts and analyze them
            final Iterator<Map.Entry<IndefinitePart, BigInteger>> entryIter =
                this.simpleMonomials.entrySet().iterator();

            // take care of the 1st addend ...
            final Map.Entry<IndefinitePart, BigInteger> addend1 = entryIter.next();
            final Pair<GENode, GENode> pair1 = this.addendToPair(addend1);
            if (pair1 == null) {
                return null;
            } else { // one of them is null
                node1 = pair1.x; // a_i
                node2 = pair1.y; // a_j or -n (node the implicit minus sign in front of node 2)
            }

            // ... then of the 2nd addend
            final Map.Entry<IndefinitePart, BigInteger> addend2 = entryIter.next();
            final Pair<GENode, GENode> pair2 = this.addendToPair(addend2);
            if (pair2 == null) {
                return null;
            } else if (pair2.x != null) {
                node1 = pair2.x;
            } else {
                if (Globals.useAssertions) {
                    assert (pair2.y != null);
                } // pair2 contains s.th., but not in its 1st component

                // so node2 and pair2.y are non-null.
                // negate the one that is a number and move it to node1.
                if (node2 != null) {
                    if (node2.isNumerical()) {
                        node1 = GENode.create(node2.number.negate());
                        node2 = pair2.y;
                    } else {
                        assert pair2.y.isNumerical();
                        node1 = GENode.create(pair2.y.number.negate());
                    }
                } else {
                    node2 = pair2.y;
                }
            }
            break;
        }
        default: // unsuitable number of addends (zero addends don't help either)
            return null;
        }

        // check whether we have a decent result
        if ((node1 != null) && (node2 != null)) {
            return new Pair<GENode, GENode>(node1, node2);
        } else {
            return null;
        }
    }

    /**
     * Strips the exponents of this to one. E.g., 9*a_1^2 + 23*a_1 + 15*a_2^5 +
     * 7 becomes 32*a_1 + 15*a_2 + 7.
     * @return this with its exponents all stripped to one
     */
    public SimplePolynomial stripExponents() {
        Map<IndefinitePart, BigInteger> result;
        result = new LinkedHashMap<IndefinitePart, BigInteger>(this.simpleMonomials.size());
        for (final Map.Entry<IndefinitePart, BigInteger> e : this.simpleMonomials.entrySet()) {
            final IndefinitePart oldIP = e.getKey();
            final IndefinitePart newIP = oldIP.copyWithFixedExponent(1);
            final BigInteger oldFactor = result.get(newIP);
            if (oldFactor == null) {
                // newIP does not occur in result so far
                result.put(newIP, e.getValue());
            } else {
                final BigInteger newFactor = e.getValue().add(oldFactor);
                if (newFactor.signum() == 0) {
                    result.remove(newIP);
                } else {
                    result.put(newIP, newFactor);
                }
            }
        }
        return SimplePolynomial.create(result);
    }

    /**
     * Strips the addends of this of their numerical factors and exponents.
     * Then, the resulting monomials are returned as a set. E.g., 9*a_1^2 +
     * 23*a_1 + 7 becomes {a_1, 1}.
     * @return set of the monomials of this with factors and exponents all
     * stripped to one
     */
    public Set<SimplePolynomial> stripFactorsExponentsAndSums() {
        final Set<SimplePolynomial> result = new LinkedHashSet<SimplePolynomial>(this.simpleMonomials.size());
        for (final IndefinitePart ip : this.simpleMonomials.keySet()) {
            Map<IndefinitePart, BigInteger> spMap;
            spMap = Collections.<IndefinitePart, BigInteger>singletonMap(ip.copyWithFixedExponent(1), BigInteger.ONE);
            final SimplePolynomial sp = SimplePolynomial.create(spMap);
            result.add(sp);
        }
        return result;
    }

    /**
     * @param zeroIndefinites indefinites whose product is supposed to be equal
     * to zero such that all addends of this that contain all members of
     * zeroIndefinites can be removed
     * @return the result of removing all addends that contain all of the
     * indefinites in zeroIndefinites from this.
     */
    SimplePolynomial eliminateAddendsThatContainAll(final Set<String> zeroIndefinites, final Abortion aborter)
        throws AbortionException
        {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        aborter.checkAbortion();
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey();
            if (!key.containsAll(zeroIndefinites)) {
                // we cannot say for sure that key is zero, so keep it
                result.put(key, entry.getValue());
            }
        }
        return SimplePolynomial.create(result);
        }

    /**
     * Return null if this has a nonzero numerical addend; otherwise return a
     * Set of SimplePolyConstraint where for each IndefinitePart of this, a new
     * one is generated with the same variables, but exponents set to one, which
     * is then used as a LHS of a SimplePolyConstraint of type EQ. Applicable
     * for simplifying a SimplePolyConstraint whose LHS (this) consists of
     * simpleMonomials (addends) that only have negative factors and which is of
     * type GE (or EQ, in this case the sign of the factors does not matter as
     * long as it is constant over all addends of this). Use only if
     * (this.allNegative() || this.allPositive()) holds.
     * @return the Set of SimplePolyConstraints that follow from a
     * SimplePolyConstraint of type GE with this as LHS where this.allNegative()
     * == true or of type EQ with (this.allPositive() || this.allNegative()) ==
     * true
     */
    Set<SimplePolyConstraint> addendsToConstraintsForConstantSign() {
        if (Globals.useAssertions) {
            assert (this.allNegative() || this.allPositive());
        }
        Set<SimplePolyConstraint> result;

        if (this.simpleMonomials.containsKey(IndefinitePart.ONE)) {
            // z \in Z for z != 0 is an addend => constraint unsatisfiable
            return null;
        } else {
            result = new LinkedHashSet<SimplePolyConstraint>(this.simpleMonomials.size());
            for (final IndefinitePart key : this.simpleMonomials.keySet()) {
                Map<IndefinitePart, BigInteger> addMe;
                IndefinitePart newIndefinitePart;

                // clone key, but with all exponents == 1.
                newIndefinitePart = key.copyWithFixedExponent(1);

                addMe = Collections.<IndefinitePart, BigInteger>singletonMap(newIndefinitePart, BigInteger.ONE);
                result.add(new SimplePolyConstraint(new SimplePolynomial(addMe), ConstraintType.EQ));
            }
            return result;
        }
    }

    /**
     * Simplifies a SimplePolyConstraint with one numerical and one
     * non-numerical addend in which this occurs on the LHS. To be called /only/
     * if this consists of one numerical and one non-numerical addend, otherwise
     * arbitrarily undesired behavior may occur.
     * @return null if the numericalAddend modulo the factor of the
     * non-numerical addend is non-zero and constraintType == EQ (then the
     * constraint is unsolvable); a SimplePolyConstraint in which both numbers
     * have been "suitably" (see code) divided by the non-numerical addend
     * otherwise (multiplied with -1 in case of constraintType == GE and
     * numerical addend > 0).
     */
    SimplePolyConstraint simplifyConstraintWithANumericalAndAnotherAddend(final ConstraintType constraintType) {
        // for constraintType == EQ
        // if numericalAddend % factorOfNonNumericalAddend == 0 then
        //     numericalAddend = numericalAddend / factorOfNonNumericalAddend
        // else inconsistent

        if (Globals.useAssertions) {
            assert (this.numberOfAddends() == 2);
            assert (this.simpleMonomials.get(IndefinitePart.ONE) != null);
        }

        BigInteger numericalAddend = BigInteger.ZERO;
        BigInteger factorOfNonNumericalAddend = BigInteger.ZERO;
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        // to be returned (as SimplePolyConstraint of type constraintType)

        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey();
            if (key.isEmpty()) { // numerical addend
                numericalAddend = entry.getValue();
            } else { // non-numerical addend
                factorOfNonNumericalAddend = entry.getValue();
            }
        }
        if (constraintType == ConstraintType.GE) {
            if (numericalAddend.signum() < 0) {
                for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
                    final IndefinitePart key = entry.getKey();
                    if (key.isEmpty()) {
                        if (numericalAddend.remainder(factorOfNonNumericalAddend).signum() == 0) {
                            result.put(key, numericalAddend.divide(factorOfNonNumericalAddend));
                        } else { // note the round-towards-zero semantics of the / operator
                            result
                            .put(key, numericalAddend.divide(factorOfNonNumericalAddend).subtract(BigInteger.ONE));
                        }
                    } else {
                        result.put(key, BigInteger.ONE); // factor / factor == 1
                    }
                }
            } else {
                for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
                    final IndefinitePart key = entry.getKey();
                    if (key.isEmpty()) {
                        result.put(key, numericalAddend.divide(factorOfNonNumericalAddend).negate());
                    } else {
                        result.put(key, BigInteger.valueOf(-1)); // factor / factor == 1, and >= becomes <=
                    }
                }
            }
            return new SimplePolyConstraint(SimplePolynomial.create(result), constraintType);
        } else if (numericalAddend.remainder(factorOfNonNumericalAddend).signum() == 0) {
            if (Globals.useAssertions) {
                assert (constraintType == ConstraintType.EQ);
            }
            for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
                final IndefinitePart key = entry.getKey();
                if (key.isEmpty()) {
                    result.put(key, numericalAddend.divide(factorOfNonNumericalAddend));
                } else {
                    result.put(key, BigInteger.ONE); // factor / factor == 1
                }
            }
            return new SimplePolyConstraint(SimplePolynomial.create(result), constraintType);
        } else {
            return null;
        }
    }

    /**
     * @return the number of addends/monomials explicitly stored in this.
     */
    public int numberOfAddends() {
        return this.simpleMonomials.size();
    }

    /**
     * @return a Set of SimplePolyConstraints in which each occurring a_i of
     * this is constrained to be > 0.
     */
    Set<SimplePolyConstraint> getConstraintsAllIndefinitesGT0() {
        final Set<SimplePolyConstraint> result = new LinkedHashSet<SimplePolyConstraint>();
        for (final String indefinite : this.getIndefinites()) {
            Map<String, Integer> exponents;
            IndefinitePart indefinitePart;
            final Map<IndefinitePart, BigInteger> simpleMonomials = new LinkedHashMap<IndefinitePart, BigInteger>(2);
            SimplePolyConstraint constraint;

            exponents = Collections.<String, Integer>singletonMap(indefinite, 1);
            indefinitePart = new IndefinitePart(exponents);
            simpleMonomials.put(indefinitePart, BigInteger.ONE);
            simpleMonomials.put(IndefinitePart.ONE, BigInteger.valueOf(-1));
            constraint = new SimplePolyConstraint(SimplePolynomial.create(simpleMonomials), GE);

            result.add(constraint);
        }
        return result;
    }

    /**
     * Computes the indefinite factors that occur in each of the addends of this
     * together with their exponents.
     * @return the IndefinitePart that encapsulates the common indefinite
     * factors of this
     */
    public IndefinitePart computeCommonFactors() {
        Map<String, Integer> result; // to be returned (as IndefinitePart)

        result = null; // means: nothing computed so far for result

        for (final IndefinitePart key : this.simpleMonomials.keySet()) {
            result = key.computeGCD(result);
            // result is reduced each iteration such that it is
            // the greatest common divisor of result and key.
        }
        return new IndefinitePart(result);
    }

    /**
     * Computes the indefinite factors that occur in each of the addends of this
     * together with their exponents reduced by one.
     * @return the IndefinitePart that encapsulates the common indefinite
     * factors of this with their exponents reduced by one
     */
    public IndefinitePart computeCommonFactorsPowersMinusOne() {
        Map<String, Integer> result; // to be returned (as IndefinitePart)

        result = null; // means: nothing computed so far for result

        for (final IndefinitePart key : this.simpleMonomials.keySet()) {
            result = key.computeGCD(result);
            // result is reduced each iteration such that it is
            // the greatest common divisor of result and key.
        }

        // now decrement the exponents of the common factors
        final Iterator<Map.Entry<String, Integer>> entryIter = result.entrySet().iterator();
        Map.Entry<String, Integer> entry;
        while (entryIter.hasNext()) {
            entry = entryIter.next();
            final int value = entry.getValue();
            if (value == 1) {
                entryIter.remove();
            } else {
                entry.setValue(value - 1);
            }
        }
        return new IndefinitePart(result);
    }

    /**
     * Tries to divide this by denominator.
     * @param denominator the denominator by which we want to divide.
     * @return this / denominator if denominator | this; otherwise, null is
     * returned.
     */
    public SimplePolynomial divide(final IndefinitePart denominator) {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey();
            final IndefinitePart newIndefinitePart = key.divide(denominator);
            if (newIndefinitePart == null) {
                return null;
            } else {
                result.put(newIndefinitePart, entry.getValue());
            }
        }
        return SimplePolynomial.create(result);
    }

    /**
     * Divides this by denominator with all its explicit exponents treated as
     * reduced by one and returns the resulting SimplePolynomial. It is
     * *required* that denominator is a divisor of all addends of this, the
     * result is undefined otherwise (and Exceptions may occur).
     * @param denominator the denominator by which this is to be "divided", must
     * be a divisor of all addends of this
     * @return the resulting SimplePolynomial: this divided by denominator with
     * its exponents treated as reduced by one before dividing
     */
    public SimplePolynomial divideWithDenominatorPowersMinusOne(final IndefinitePart denominator) {
        final Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>();
        // to be returned (as SimplePolynomial)

        // for all monomials/addends of this ...
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey();
            final BigInteger value = entry.getValue();
            IndefinitePart newIndefinitePart;

            // ... perform the divisions individually
            newIndefinitePart = key.divideWithDenominatorMinusOne(denominator);
            result.put(newIndefinitePart, value);
        }

        return SimplePolynomial.create(result);
    }

    /**
     * Returns this.simpleMonomials. Needed by VarPolynomial and the SatSearch
     * classes.
     * @return this.simpleMonomials.
     */
    public ImmutableMap<IndefinitePart, BigInteger> getSimpleMonomials() {
        return this.simpleMonomials;
    }

    /**
     * Returns an overapproximation of the maximum value this may assume given
     * values. Note: Assumes for all elemente interval of values.values(): 0 <=
     * interval.min <= interval.max
     * @param values maps indefinites to integer intervals with possible values,
     * must assign non-null values to all variables of this
     * @return the maximum value this can take given values
     */
    public BigInteger max(final Map<String, BigIntegerInterval> values) {
        BigInteger result = BigInteger.ZERO;
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final BigInteger factor = entry.getValue();
            final int signum = factor.signum();
            if (signum > 0) {
                result = result.add(entry.getKey().max(values).multiply(factor));
            } else if (signum < 0) {
                result = result.add(entry.getKey().min(values).multiply(factor));
            }
        }
        return result;
    }

    /**
     * Returns an underapproximation of the minimum value this may assume given
     * values. Note: Assumes for all elemente interval of values.values(): 0 <=
     * interval.min <= interval.max
     * @param values maps indefinites to integer intervals with possible values,
     * must assign non-null values to all variables of this
     * @return the minimum value this can take given values
     */
    public BigInteger min(final Map<String, BigIntegerInterval> values) {
        BigInteger result = BigInteger.ZERO;
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final BigInteger factor = entry.getValue();
            final int signum = factor.signum();
            if (signum > 0) {
                result = result.add(entry.getKey().min(values).multiply(factor));
            } else if (signum < 0) {
                result = result.add(entry.getKey().max(values).multiply(factor));
            }
        }
        return result;
    }

    /**
     * Counts how many times a product a_i * a_j or a_i^2 occurs in this and
     * increments the values of the mapping products accordingly.
     * @param products mapping [StringPair -> Integer] which keeps track of how
     * many times a product of two variables (stored in the key of the mapping)
     * has been observed. Note that the second variable of the StringPair is
     * never smaller than the first one with respect to the natural order of
     * String.
     */
    public void getProducts(final Map<StringPair, Integer> products) {
        for (final IndefinitePart indefinitePart : this.simpleMonomials.keySet()) {
            indefinitePart.getProducts(products);
        }
    }

    /**
     * Returns a version of this in which x^2 is replaced by z. products is
     * modified accordingly in the process.
     * @param x x^2 is to be replaced in this
     * @param z replacement for x^2
     * @param products keeps track of how often each product of two indefinites
     * occurs in the system (map StringPair -> Integer), is modified to suit a
     * replacement of this by the returned SimplePolynomial; (x, x) is assumed
     * not to occur in products any more when replaceSquares(...) is called
     * @return the SimplePolynomial in which all occurrences of x^2 are replaced
     * by z (apart from that, it is like this)
     */
    public SimplePolynomial replaceSquares(final String x, final String z, final Map<StringPair, Integer> products) {
        if (!this.containsIndefinite(x)) {
            return this;
        }

        final Map<IndefinitePart, BigInteger> result =
            new LinkedHashMap<IndefinitePart, BigInteger>(this.simpleMonomials.size());
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            result.put(entry.getKey().replaceSquares(x, z, products), entry.getValue());
        }
        return SimplePolynomial.create(result);
    }

    /**
     * Returns a version of this in which x*y is replaced by z. Modifies
     * products accordingly.
     * @param x one of the two factors of the product which is to be replaced
     * @param y the other factor of the product which is to be replaced
     * @param z replacement for x*y
     * @param products keeps track of how often each product of two variables
     * occurs in the system (map StringPair -> Integer), is modified to suit the
     * changes that follow from replacing this by the returned SimplePolynomial;
     * (x, y) is assumed not to occur in products any more when
     * replaceProducts(...) is called
     * @return the SimplePolynomial in which all occurrences of x*y are replaced
     * by z (apart from that, it is like this)
     */
    public SimplePolynomial replaceProducts(
        final String x,
        final String y,
        final String z,
        final Map<StringPair, Integer> products)
    {
        if ((!this.containsIndefinite(x)) || (!this.containsIndefinite(y))) {
            return this;
        }

        final Map<IndefinitePart, BigInteger> result =
            new LinkedHashMap<IndefinitePart, BigInteger>(this.simpleMonomials.size());
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            result.put(entry.getKey().replaceProducts(x, y, z, products), entry.getValue());
        }
        return SimplePolynomial.create(result);
    }

    /**
     * Assuming a SimplePolyConstraint (this = 0), the corresponding
     * FiniteDomains are created (according to Def. 4.3 of the paper where the
     * search is presented) and added to fdc.
     * @param fdc the resulting FiniteDomains are added to fdc
     */
    public void getEqualityConstraints(final FDConstraints fdc) {
        // for all monomials in this ...
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey(); // monomial indefinites
            final BigInteger value = entry.getValue(); // numerical monomial coefficient
            if (key.isEmpty()) { // constant addend
                continue;
            }
            final Map<IndefinitePart, BigInteger> numeratorMap =
                new LinkedHashMap<IndefinitePart, BigInteger>(this.simpleMonomials);
            numeratorMap.remove(key);

            if (value.signum() > 0) {
                // negate numerator
                for (final Map.Entry<IndefinitePart, BigInteger> numeratorEntry : numeratorMap.entrySet()) {
                    numeratorEntry.setValue(numeratorEntry.getValue().negate());
                }
            }
            final SimplePolynomial numerator = new SimplePolynomial(numeratorMap);

            // for all ways to split off one indefinite (with its power)
            // from the rest of the IndefinitePart ...
            for (final Triple<IndefinitePart, String, Integer> split : key.getSplits()) {
                final int exponent = split.z;
                FDBoundary lowerBound, upperBound;
                SimplePolynomial denominator = null;
                final BigInteger absValue = value.abs();
                if (split.x.isEmpty()) {
                    if (!absValue.equals(BigInteger.ONE)) {
                        denominator = new SimplePolynomial(absValue);
                    }
                } else {
                    final Map<IndefinitePart, BigInteger> simpleMonomials =
                        Collections.<IndefinitePart, BigInteger>singletonMap(split.x, absValue);
                    denominator = new SimplePolynomial(simpleMonomials);
                }

                lowerBound = FDBoundary.create(numerator, denominator, exponent);
                //upperBound = FDBoundary.create(numerator, denominator, exponent);
                upperBound = lowerBound;

                final FiniteDomain fd = FiniteDomain.create(split.y, lowerBound, upperBound);

                fdc.addConstraint(fd);
            }
        }
    }

    /**
     * Assuming a SimplePolyConstraint (this >= 0), the corresponding
     * FiniteDomains are created (according to Def. 4.3 of the paper where the
     * search is presented) and added to fdc.
     * @param fdc the resulting FiniteDomains are added to fdc, and the upper
     * bound for the resulting FiniteDomains is taken from fdc
     * @param isSearchStrict whether this is the LHS of a searchStrict
     * constraint; if so, fdc.searchStrictFDs will be modified accordingly
     */
    public void getInequalityConstraints(final FDConstraints fdc, final boolean isSearchStrict) {
        // map the FiniteDomains that are constructed here to whether
        // it is their *lower* bound that might get changed by searchstrict
        Map<FiniteDomain, Boolean> finiteDomains;
        finiteDomains = new LinkedHashMap<FiniteDomain, Boolean>(8 * this.simpleMonomials.size());

        // for all monomials in this ...
        for (final Map.Entry<IndefinitePart, BigInteger> entry : this.simpleMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey(); // monomial indefinites
            if (key.isEmpty()) { // constant addend
                continue;
            }
            final BigInteger value = entry.getValue(); // numerical monomial coefficient
            final boolean valueGT0 = value.signum() > 0;
            // If valueGT0, then we have to modify the lower bound of the
            // resulting FiniteDomain for making the corresponding
            // constraint strict, which might become necessary if it is
            // a searchStrict constraint. Otherwise it is the upperBound.

            final Map<IndefinitePart, BigInteger> numeratorMap =
                new LinkedHashMap<IndefinitePart, BigInteger>(this.simpleMonomials);
            numeratorMap.remove(key);

            if (valueGT0) {
                // negate numerator
                for (final Map.Entry<IndefinitePart, BigInteger> numeratorEntry : numeratorMap.entrySet()) {
                    numeratorEntry.setValue(numeratorEntry.getValue().negate());
                }
            }
            final SimplePolynomial numerator = new SimplePolynomial(numeratorMap);

            // for all ways to split off one indefinite (with its power)
            // from the rest of the IndefinitePart ...
            for (final Triple<IndefinitePart, String, Integer> split : key.getSplits()) {
                final int exponent = split.z;
                FDBoundary lowerBound, upperBound;
                SimplePolynomial denominator = null;
                final BigInteger absValue = value.abs();
                if (split.x.isEmpty()) {
                    if (!absValue.equals(BigInteger.ONE)) {
                        denominator = new SimplePolynomial(absValue);
                    }
                } else {
                    final Map<IndefinitePart, BigInteger> simpleMonomials =
                        Collections.<IndefinitePart, BigInteger>singletonMap(split.x, absValue);
                    denominator = new SimplePolynomial(simpleMonomials);
                }

                if (valueGT0) {
                    lowerBound = FDBoundary.create(numerator, denominator, exponent);
                    upperBound = FDBoundary.create(new SimplePolynomial(fdc.ranges.get(split.y)));
                } else {
                    lowerBound = FDBoundary.create(SimplePolynomial.ZERO);
                    upperBound = FDBoundary.create(numerator, denominator, exponent);
                }

                final FiniteDomain fd = FiniteDomain.create(split.y, lowerBound, upperBound);
                finiteDomains.put(fd, valueGT0);
            }
        }
        fdc.addConstraints(finiteDomains, isSearchStrict);
    }

    /**
     * @return whether this is linear (i.e., every monomial contains at most one
     * indefinite and any occurrence of an indefinite has exponent 1)
     */
    public boolean isLinear() {
        for (final Entry<IndefinitePart, BigInteger> monomial : this.simpleMonomials.entrySet()) {
            final IndefinitePart ip = monomial.getKey();
            if (!ip.isLinear()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return whether this is strongly linear (i.e., only contains monomials of degree 1 with coefficient 1 or of
     * degree 0 with arbitrary coefficient)
     */
    public boolean isStronglyLinear() {
        for (final Entry<IndefinitePart, BigInteger> monomial : this.simpleMonomials.entrySet()) {
            final IndefinitePart ip = monomial.getKey();
            if (!ip.isEmpty() && !monomial.getValue().equals(BigInteger.ONE)) {
                return false;
            }
            if (!ip.isLinear()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return whether this encodes just a numerical constant
     */
    public boolean isConstant() {
        final int size = this.simpleMonomials.size();
        return ((size == 0) || ((size == 1) && this.simpleMonomials.containsKey(IndefinitePart.ONE)));
    }

    /**
     * If this polynomial is a constant, return its {@link BigInteger} representation, otherwise return {@code null}.
     * @return
     */
    public BigInteger getConstantSize() {
        final int size = this.simpleMonomials.size();
        switch (size) {
        case 0:
            return BigInteger.ZERO;
        case 1:
            return this.simpleMonomials.get(IndefinitePart.ONE);
        default:
            return null;
        }
    }

    /**
     * @return whether this encodes one indefinite at power 1
     */
    public boolean isIndefinite() {
        if (this.simpleMonomials.size() == 1) {
            final Entry<IndefinitePart, BigInteger> entrie = this.simpleMonomials.entrySet().iterator().next();
            return (entrie.getValue().equals(BigInteger.ONE) && entrie.getKey().isIndefinite());
        } else {
            return false;
        }
    }

    /**
     * Increments counts by the number of occurrences of the respective
     * indefinite in this (disregarding exponents)
     * @param counts keeps track of how often indefinites occur (without taking
     * into account the power at which they occur)
     */
    public void countIndefinites(final Map<String, Integer> counts) {
        for (final IndefinitePart iPart : this.simpleMonomials.keySet()) {
            iPart.countIndefinites(counts);
        }
    }

    /**
     * @param x indefinite to be checked for containment in this
     * @return whether x occurs in this
     */
    public boolean containsIndefinite(final String x) {
        for (final IndefinitePart iPart : this.simpleMonomials.keySet()) {
            if (iPart.contains(x)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Interesting for SatSearch.
     * @return given this == p - q where p and q are polys whose monomials only
     * have positive factor, (p,q) is returned
     */
    public Pair<SimplePolynomial, SimplePolynomial> toPositivePair() {
        Map<IndefinitePart, BigInteger> lhs, rhs;
        lhs = new LinkedHashMap<IndefinitePart, BigInteger>();
        rhs = new LinkedHashMap<IndefinitePart, BigInteger>();

        for (final Map.Entry<IndefinitePart, BigInteger> e : this.simpleMonomials.entrySet()) {
            final BigInteger factor = e.getValue();
            if (factor.signum() > 0) {
                lhs.put(e.getKey(), factor);
            } else {
                rhs.put(e.getKey(), factor.negate());
            }
        }
        return new Pair<SimplePolynomial, SimplePolynomial>(SimplePolynomial.create(lhs), SimplePolynomial.create(rhs));
    }

    /**
     * Computes the value this takes under <code>interpretation</code>.
     * <code>defaultValue</code> is used for all those indefinites that do not
     * occur as keys of interpretation.
     * @param interpretation assigns numbers to the indefinites of this
     * @param defaultValue used for indefinites for which interpretation does
     * not contain any values
     * @return the resulting number
     */
    public BigInteger interpret(final Map<String, BigInteger> interpretation, final BigInteger defaultValue) {
        BigInteger result = BigInteger.ZERO;
        for (final Map.Entry<IndefinitePart, BigInteger> e : this.simpleMonomials.entrySet()) {
            final BigInteger factor = e.getValue();
            final BigInteger interpretedIPart = e.getKey().interpret(interpretation, defaultValue);
            result = result.add(factor.multiply(interpretedIPart));
        }
        return result;
    }

    /**
     * Compares two SimplePolynomials lexicographically. In ascending order wrt
     * the natural order on IndefiniteParts, we check which of the two
     * IndefiniteParts is the greater one; if they are equal, we check which of
     * the corresponding factors is bigger; if they are equal as well, we
     * proceed to the next IndefinitePart if existant. In the end, we check
     * whether one of the SimplePolynomials is a proper prefix of the other. If
     * not, they must be equal. E.g.: 2*x*y < 3*x*y < 2*x*z < 2*x*z+x^2*z^2
     * @see java.lang.Comparable#compareTo(SimplePolynomial)
     * @param other
     * @return
     */
    @Override
    public int compareTo(final SimplePolynomial other) {
        SortedMap<IndefinitePart, BigInteger> m1, m2;
        m1 = new TreeMap<IndefinitePart, BigInteger>(this.simpleMonomials);
        m2 = new TreeMap<IndefinitePart, BigInteger>(other.simpleMonomials);

        Iterator<Map.Entry<IndefinitePart, BigInteger>> iter1, iter2;
        iter1 = m1.entrySet().iterator();
        iter2 = m2.entrySet().iterator();

        Map.Entry<IndefinitePart, BigInteger> e1, e2;
        while (iter1.hasNext() && iter2.hasNext()) {
            e1 = iter1.next();
            e2 = iter2.next();

            IndefinitePart key1, key2;
            key1 = e1.getKey();
            key2 = e2.getKey();

            int indefPartDifference;
            indefPartDifference = key1.compareTo(key2);
            if (indefPartDifference < 0) {
                return -1;
            } else if (indefPartDifference > 0) {
                return 1;
            } else {
                BigInteger factorDifference;
                factorDifference = e1.getValue().subtract(e2.getValue());
                if (factorDifference.signum() < 0) {
                    return -1;
                } else if (factorDifference.signum() > 0) {
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
    public int hashCode() {
        if (this.hashValid) {
            return this.hashValue;
        }
        this.computeHashValue();
        return this.hashValue;
    }

    private void computeHashValue() {
        this.hashValue = this.simpleMonomials.hashCode();
        this.hashValid = true;
    }

    @Override
    public boolean equals(final Object o) {
        SimplePolynomial simplePoly;

        if (!(o instanceof SimplePolynomial)) {
            return false;
        }
        simplePoly = (SimplePolynomial) o;

        // profit from our cached hash value
        if (simplePoly.hashCode() != this.hashCode()) {
            return false;
        }
        return (simplePoly.simpleMonomials.equals(this.simpleMonomials));
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(final Export_Util eu) {
        return this.export(eu, new LinkedHashMap<String, String>(0));
    }

    public String export(final Export_Util eu, final Map<String, String> repr) {
        if (this.simpleMonomials.isEmpty()) {
            return "0";
        }
        StringBuilder buffer;
        buffer = new StringBuilder(16 * this.simpleMonomials.size());
        Iterator<Map.Entry<IndefinitePart, BigInteger>> iter;
        SortedMap<IndefinitePart, BigInteger> m;
        m = new TreeMap<IndefinitePart, BigInteger>(this.simpleMonomials);
        iter = m.entrySet().iterator();
        while (iter.hasNext()) {
            final Map.Entry<IndefinitePart, BigInteger> entry = iter.next();
            final BigInteger value = entry.getValue();
            final IndefinitePart key = entry.getKey();
            final boolean keyIsOne = key.equals(IndefinitePart.ONE);
            if (!value.equals(BigInteger.ONE)) {
                buffer.append(value);
                if (!keyIsOne) {
                    buffer.append(eu.multSign());
                    buffer.append(key.export(eu, repr));
                }
            } else {
                if (keyIsOne) {
                    buffer.append(value);
                } else {
                    buffer.append(key.export(eu, repr));
                }
            }
            if (iter.hasNext()) {
                buffer.append(" + ");
            }
        }
        return buffer.toString();
    }

    public String toStringRep(final PolyFormatter format) {
        if (this.simpleMonomials.isEmpty()) {
            return "0";
        }
        final StringBuilder buffer = new StringBuilder();
        boolean inString = false;

        for (final Map.Entry<IndefinitePart, BigInteger> e : this.simpleMonomials.entrySet()) {
            final BigInteger coeff = e.getValue();
            final IndefinitePart monom = e.getKey();
            if (inString) {
                buffer.append(" + "); // Maybe at some point we need this from the PolyFormatter too
            }
            inString = true;
            if (monom.equals(IndefinitePart.ONE)) {
                buffer.append(coeff);
            } else {
                if (!coeff.equals(BigInteger.ONE)) {
                    buffer.append(coeff);
                    buffer.append(format.getMult());
                }
                buffer.append(monom.toStringRep(format));
            }
        }
        return buffer.toString();
    }

    public String toSicstusProlog() {
        return this.toStringRep(PolyFormatter.PROLOG);
    }

    public String toCiME() {
        return this.toStringRep(PolyFormatter.CIME);
    }

    /**
     * @return a term representation of this where the monomials are ordered in their natural order.
     */
    public TRSTerm toOrderedTerm() {
        SimplePolynomial ordered = new SimplePolynomial(new TreeMap<>(this.simpleMonomials));
        return ordered.toTerm();
    }

    /**
     * Returns a term representation of this.
     * @param predefMap some predefined map
     * @return term
     */
    public TRSTerm toTerm(final IDPPredefinedMap predefined) {
        if (this.isZero()) {
            return predefined.getIntTerm(BigIntImmutable.ZERO, DomainFactory.INTEGERS);
        }

        TRSTerm result = null;

        for (final Entry<IndefinitePart, BigInteger> e : this.simpleMonomials.entrySet()) {
            final IndefinitePart indefPart = e.getKey();
            final BigInteger bigInt = e.getValue();

            TRSTerm current;
            boolean coefficientIsOne = bigInt.equals(BigInteger.ONE);
            boolean indefIsOne = indefPart.equals(IndefinitePart.ONE);
            if (coefficientIsOne && indefIsOne) {
                current = predefined.getIntTerm(BigIntImmutable.create(BigInteger.ONE), DomainFactory.INTEGERS);
            } else if (!coefficientIsOne && !indefIsOne) {
                final TRSTerm coefficientTerm = predefined.getIntTerm(BigIntImmutable.create(bigInt), DomainFactory.INTEGERS);
                final TRSTerm indefTerm = indefPart.toTerm(predefined);
                current = TRSTerm.createFunctionApplication(
                                predefined.getSym(Func.Mul, DomainFactory.INTEGERS),
                                coefficientTerm,
                                indefTerm);
            } else if (coefficientIsOne) {
                current = indefPart.toTerm(predefined);
            } else {
                assert indefIsOne;
                current = predefined.getIntTerm(BigIntImmutable.create(bigInt), DomainFactory.INTEGERS);
            }

            if (result == null) {
                result = current;
            } else {
                result =
                    TRSTerm.createFunctionApplication(
                        predefined.getSym(Func.Add, DomainFactory.INTEGERS),
                        result,
                        current);
            }
        }

        result = result == null ? predefined.getIntTerm(BigIntImmutable.ZERO, DomainFactory.INTEGERS) : result;

        return result;
    }

    /**
     * Returns a term representation of this. This imlementation uses the
     * default predefined map.
     * @return term
     */
    public TRSTerm toTerm() {
        return this.toTerm(IDPPredefinedMap.DEFAULT_MAP);
    }

    public SMTLIBIntValue toSMTLIB() {
        if (this.simpleMonomials.isEmpty()) {
            return SMTLIBIntConstant.create(BigInteger.ZERO);
        }
        final List<SMTLIBIntValue> monomialsSMT = new ArrayList<SMTLIBIntValue>(this.simpleMonomials.size());
        for (final Map.Entry<IndefinitePart, BigInteger> e : this.simpleMonomials.entrySet()) {
            final IndefinitePart iPart = e.getKey();
            final BigInteger coeff = e.getValue();
            final SMTLIBIntValue monomialSMT;
            if (iPart.isEmpty()) {
                monomialSMT = SMTLIBIntConstant.create(coeff);
            } else if (coeff.equals(BigInteger.ONE)) {
                monomialSMT = iPart.toSMTLIB();
            } else {
                final List<SMTLIBIntValue> protoMonomialSMT = new ArrayList<SMTLIBIntValue>(2);
                protoMonomialSMT.add(SMTLIBIntConstant.create(coeff));
                protoMonomialSMT.add(iPart.toSMTLIB());
                monomialSMT = SMTLIBIntMult.create(protoMonomialSMT);
            }
            monomialsSMT.add(monomialSMT);
        }
        final int size = monomialsSMT.size();
        if (Globals.useAssertions) {
            assert size > 0;
        }
        final SMTLIBIntValue res = size > 1 ? SMTLIBIntPlus.create(monomialsSMT) : monomialsSMT.get(0);
        return res;
    }

    /**
     * Export polynomial to SMT Formula for the aprove.verification.oldframework.SMT framework.
     * @param variables If a variable is contained in this map, its symbol is
     * used. Otherwise, a fresh symbol is added to this map and used.
     * @return
     */
    public SMTExpression<SInt> toSMT(final VariableScope scope) {
        final ArrayList<SMTExpression<SInt>> sum = new ArrayList<>();
        for (final Map.Entry<IndefinitePart, BigInteger> e : this.simpleMonomials.entrySet()) {
            final IndefinitePart iPart = e.getKey();
            final BigInteger coeff = e.getValue();
            final ArrayList<SMTExpression<SInt>> product = new ArrayList<>();
            if (!BigInteger.ONE.equals(coeff)) {
                product.add(Ints.constant(coeff));
            }
            for (final Entry<String, Integer> ve : iPart.getExponents().entrySet()) {
                final Symbol0<SInt> v = scope.intVar(ve.getKey());
                for (int i = 0, l = ve.getValue(); i < l; ++i) {
                    product.add(v);
                }
            }
            sum.add(Ints.times(product));
        }
        return Ints.add(sum);
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        return XMLTag.createInteger(doc, this.getNumericalAddend().toString());
    }

    public Element toCPF(final Document doc) {
        return CPFTag.INTEGER.create(doc, this.getNumericalAddend());
    }

    public Element toLtsCPF(final Document doc) {
        return CPFTag.CONSTANT.create(doc, this.getNumericalAddend());
    }

    public Element toRatCPF(final Document doc, final int denominator) {
        return CPFTag.RATIONAL.create(
            doc,
            CPFTag.NUMERATOR.create(doc, this.getNumericalAddend()),
            CPFTag.DENOMINATOR.create(doc, denominator));
    }

    public Element toDIODOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element sumTag = XMLTag.DIO_SUM.createElement(doc);
        for (final Map.Entry<IndefinitePart, BigInteger> entry : new TreeMap<IndefinitePart, BigInteger>(
            this.simpleMonomials).entrySet())
        {
            final Element productTag = XMLTag.DIO_PRODUCT.createElement(doc);
            productTag.appendChild(XMLTag.createInteger(doc, entry.getValue().toString()));
            productTag.appendChild(XMLTag.createInteger(doc, entry.getKey().toString()));
            sumTag.appendChild(productTag);
        }
        return sumTag;
    }

    /**
     * Compute the degree of the polynomial.
     * @return The degree of the polynomial
     */
    public int getDegree() {
        int maxDegree = 0;
        for (final IndefinitePart indef : this.simpleMonomials.keySet()) {
            maxDegree = Math.max(maxDegree, indef.getDegree());
        }
        return maxDegree;
    }


    /**
     * @return Set of all variables that occure in this
     */
    public Set<String> getVariables() {
        final Set<String> variables = new HashSet<>();
        for (final IndefinitePart indef : this.getIndefiniteParts()) {
            variables.addAll(indef.getIndefinites());
        }
        return variables;
    }

    public SimplePolynomial replace(final Map<String, String> renamingMap) {
        final Map<IndefinitePart, BigInteger> monomials = new HashMap<>();
        for (final Entry<IndefinitePart, BigInteger> entry : this.getSimpleMonomials().entrySet()) {
            monomials.put(entry.getKey().replace(renamingMap), entry.getValue());
        }
        return SimplePolynomial.create(monomials);
    }

    public SimplePolynomial assign(final Map<String, SimplePolynomial> assignMap) {
        final List<SimplePolynomial> polys = new ArrayList<>();
        for (final Entry<IndefinitePart, BigInteger> entry : this.getSimpleMonomials().entrySet()) {
            final List<SimplePolynomial> indefPolys = new ArrayList<>();

            indefPolys.add(SimplePolynomial.create(entry.getValue()));

            for (final Entry<String, Integer> indefEntry : entry.getKey().getExponents().entrySet()) {
                if (assignMap.containsKey(indefEntry.getKey())) {
                    indefPolys.add(assignMap.get(indefEntry.getKey()).power(indefEntry.getValue()));
                } else {
                    indefPolys.add(SimplePolynomial.create(indefEntry.getKey()).power(indefEntry.getValue()));
                }
            }
        }
        return SimplePolynomial.times(polys);
    }

    public BigInteger tryEvaluate(final Map<String, BigInteger> valueMap) {
        BigInteger sum = BigInteger.ZERO;

        for (final Entry<IndefinitePart, BigInteger> entry : this.getSimpleMonomials().entrySet()) {
            final BigInteger value = entry.getKey().tryEvaluate(valueMap);

            if (value == null) {
                return null;
            }
            sum = sum.add(value.multiply(entry.getValue()));
        }

        return sum;
    }

    public static SimplePolynomial parse(String polyString) {
        return KoATParser.parseAsPolynomial(polyString);
    }

    public MinMaxExpr toMinMaxExpr() {
        SimplePolynomial ordered = new SimplePolynomial(new TreeMap<>(this.simpleMonomials));
        MinMaxExpr zero = MinMaxExpr.createInt(BigInteger.ZERO);
        MinMaxExpr one = MinMaxExpr.createInt(BigInteger.ONE);
        if (ordered.simpleMonomials.isEmpty()) {
            return zero;
        }
        Iterator<Entry<IndefinitePart, BigInteger>> it = ordered.simpleMonomials.entrySet().iterator();
        Entry<IndefinitePart, BigInteger> e = it.next();
        MinMaxExpr coefficient = MinMaxExpr.createInt(e.getValue());
        MinMaxExpr indef = e.getKey().toMinMaxPoly();
        MinMaxExpr res;
        if (coefficient.equals(one)) {
            res = indef;
        } else if (indef.equals(one)) {
            res = coefficient;
        } else {
            res = MinMaxExpr.createTimes(coefficient, indef);
        }
        while (it.hasNext()) {
            e = it.next();
            coefficient = MinMaxExpr.createInt(e.getValue());
            indef = e.getKey().toMinMaxPoly();
            MinMaxExpr m;
            if (indef.equals(one)) {
                m = coefficient;
            } else if (coefficient.equals(one)) {
                m = indef;
            } else {
                m = MinMaxExpr.createTimes(coefficient, indef);
            }
            if (!m.equals(zero)) {
                res = MinMaxExpr.createPlus(res, m);
            }
        }
        return res;
    }

}
