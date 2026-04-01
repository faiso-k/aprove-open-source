package aprove.verification.oldframework.Algebra.Polynomials;

import java.math.*;
import java.util.*;
import java.util.Map.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Carsten Fuhs
 * @version $Id$
 *
 * Representation of multivariate integer polynomials of arbitrary
 * degree in additive form. Distinguishes between (often implicitly universally
 * quantified) variables and (often implicitly existentially quantified)
 * indefinite coefficients (i.e., those that have not been fixed yet). Many
 * methods of the class rely on the assumption that quantification for both
 * variables and indefinite coefficients takes place only over the
 * /non-negative/ integers (whose natural ordering is well founded).
 *
 * The primary purpose of this class is to serve as a representation for
 * polynomial functions over the <b>natural</b> numbers (i.e., the non-negative
 * integers) as polynomial interpretations, both during the search for such
 * interpretations (where coefficients may contain parameters) and also for
 * concrete interpretations where the factor is known. A polynomial is
 * represented as a LinkedHashMap which maps the variable part of each monomial
 * occurring inside the polynomial given in additive form to its corresponding
 * coefficient. This coefficient is a SimplePolynomial, which is a polynomial
 * over coefficients whose values (possibly) have not yet been defined.
 *
 * Addends which effectively amount to zero are not represented explicitly
 * (of which all methods which create a VarPolynomial must take care). Addition
 * and multiplication are the standard operations. As a design decision,
 * variables are represented by Strings. Moreover, VarPolynomials are always
 * represented as sums of products of a SimplePolynomial and variables. Thus,
 * (4*a+b)*(x+y^2) will be represented as (4*a+b)*x + (4*a+b)*y^2 (here
 * "(4*a+b)" denotes a SimplePolynomial, and x and y are variables of the
 * VarPolynomial).
 *
 * Advantage: Every polynomial has a unique representation, so
 * VarPolynomial.equals() does what one would expect and does it rather quickly.
 *
 * Disadvantage: This representation may require exponentially more space than
 * allowing arbitrary combinations of sums and products. This can (obviously) be
 * quite inconvenient, but for comparing polynomial interpretations it is not
 * clear how to avoid this.
 *
 * Note for the interface Comparable: VarPolynomial.compareTo conducts a
 * comparison on /syntactic/ level, not on arithmetic level (otherwise,
 * "x" and "y" would be incomparable, which would violate the contract of
 * Comparable.
 */
public class VarPolynomial
    implements
        Immutable,
        Exportable,
        Comparable<VarPolynomial>,
        XMLObligationExportable,
        CPFAdditional
{
    private static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.VarPolynomial");

    // map the product of variables of each monomial to its coefficient
    private final ImmutableMap<IndefinitePart, SimplePolynomial> varMonomials;

    private int hashValue; // cache for the hash value
    private boolean hashValid; // has the hash value already been computed?

    public static final VarPolynomial ZERO = new VarPolynomial();
    public static final VarPolynomial ONE = new VarPolynomial(1);

    // Note that despite the existence of ZERO and ONE, you should not
    // use == comparisons on them, but equals comparison, since there can
    // be several equal objects to ZERO or ONE in the system

    /**
     * Creates a VarPolynomial which is equivalent to 0. Use VarPolynomial.ZERO
     * instead.
     */
    private VarPolynomial() {
        this.varMonomials = ImmutableCreator.create(Collections.<IndefinitePart, SimplePolynomial>emptyMap());
        this.hashValid = false;
    }

    /**
     * Creates a new SimplePolynomial with simpleMonomials as
     * coefficient-to-exponent mapping. Uses the empty mapping in case
     * simpleMonomials == null. varMonomials will not be modified by this class,
     * and it must not be modified outside of this class either. In case such
     * modifications are desired, pass a copy to the constructor.
     * @param varMonomials the coefficient-to-exponent mapping; an empty mapping
     * in case varMonomials == null
     */
    private VarPolynomial(final Map<IndefinitePart, SimplePolynomial> varMonomials) {
        if (varMonomials == null) {
            this.varMonomials = ImmutableCreator.create(Collections.<IndefinitePart, SimplePolynomial>emptyMap());
        } else {
            if (Globals.useAssertions) {
                assert (!varMonomials.values().contains(SimplePolynomial.ZERO));
            }
            this.varMonomials = ImmutableCreator.create(varMonomials);
        }
        this.hashValid = false;
    }

    /**
     * Creates a VarPolynomial which is equivalent to constant.
     * @param constant the int to be represented as VarPolynomial
     */
    private VarPolynomial(final BigInteger constant) {
        if (constant.signum() == 0) {
            this.varMonomials = ImmutableCreator.create(Collections.<IndefinitePart, SimplePolynomial>emptyMap());
        } else {
            final Map<IndefinitePart, SimplePolynomial> varMonomials =
                Collections.singletonMap(IndefinitePart.ONE, SimplePolynomial.create(constant));
            this.varMonomials = ImmutableCreator.create(varMonomials);
        }
        this.hashValid = false;
    }

    /**
     * Creates a VarPolynomial which is equivalent to constant.
     * @param constant the int to be represented as VarPolynomial
     */
    private VarPolynomial(final int constant) {
        if (constant == 0) {
            this.varMonomials = ImmutableCreator.create(Collections.<IndefinitePart, SimplePolynomial>emptyMap());
        } else {
            final Map<IndefinitePart, SimplePolynomial> varMonomials =
                Collections.singletonMap(IndefinitePart.ONE, SimplePolynomial.create(constant));
            this.varMonomials = ImmutableCreator.create(varMonomials);
        }
        this.hashValid = false;
    }

    /**
     * Creates a VarPolynomial which is equivalent to simplePoly.
     * @param simplePoly the (non-null) SimplePolynomial which is supposed to
     * make up this.
     */
    private VarPolynomial(final SimplePolynomial simplePoly) {
        Map<IndefinitePart, SimplePolynomial> varMonomials;
        if (!simplePoly.isZero()) {
            varMonomials = Collections.singletonMap(IndefinitePart.ONE, simplePoly);
        } else {
            varMonomials = Collections.emptyMap();
        }
        this.varMonomials = ImmutableCreator.create(varMonomials);
        this.hashValid = false;
    }

    static VarPolynomial create(final Map<IndefinitePart, SimplePolynomial> varMonomials) {
        return new VarPolynomial(varMonomials);
    }

    public static VarPolynomial create(final ImmutableMap<IndefinitePart, SimplePolynomial> varMonomials) {
        // method is public since the caller is naturally quite aware
        // of the parameter being Immutable
        return new VarPolynomial(varMonomials);
    }

    public static VarPolynomial create(final SimplePolynomial simplePoly) {
        return new VarPolynomial(simplePoly);
    }

    /**
     * Creates a VarPolynomial which only consists of the (non-null) variable x.
     * @param x the variable that will make up this.
     */
    public static VarPolynomial createVariable(final String x) {
        final Map<IndefinitePart, SimplePolynomial> result =
            Collections.singletonMap(new IndefinitePart(x), SimplePolynomial.ONE);
        return new VarPolynomial(result);
    }

    /**
     * Creates a VarPolynomial which only consists of the (non-null) coefficient
     * a.
     * @param a the coefficient that will make up this.
     */
    public static VarPolynomial createCoefficient(final String a) {
        final Map<IndefinitePart, SimplePolynomial> result =
            Collections.singletonMap(IndefinitePart.ONE, SimplePolynomial.create(a));
        return new VarPolynomial(result);
    }

    /**
     * @param n
     * @return a VarPolynomial which is equivalent to n
     */
    public static VarPolynomial create(final BigInteger n) {
        return new VarPolynomial(n);
    }

    /**
     * @param n
     * @return a VarPolynomial which is equivalent to n
     */
    public static VarPolynomial create(final int n) {
        switch (n) {
        case 0:
            return VarPolynomial.ZERO;
        case 1:
            return VarPolynomial.ONE;
        default:
            return new VarPolynomial(n);
        }
    }

    /**
     * Creates a VarPolynomial which represents the product of the variables xs
     * and factor.
     * @param xs set of variables which will occur at power 1 each
     * @param factor to be the factor of the result
     * @return xs * factor
     */
    public static VarPolynomial createProduct(final Set<String> xs, final SimplePolynomial factor) {
        Map<IndefinitePart, SimplePolynomial> result;
        result = Collections.singletonMap(new IndefinitePart(xs), factor);
        return new VarPolynomial(result);
    }

    /**
     * Creates a VarPolynomial representation of a given Polynomial. Assumes
     * that the given Polynomial does not contain any indefinite coefficients.
     * @param oldPoly the Polynomial from which the VarPolynomial is to be
     * created
     * @param xs the variables of the Polynomial (as opposed to its
     * coefficients)
     * @return the VarPolynomial created from the given Polynomial
     */
    public static VarPolynomial toVarPolynomial(final Polynomial oldPoly, final Set<String> xs) {
        VarPolynomial result = VarPolynomial.ZERO; // to be returned

        for (final Monomial monomial : oldPoly) {
            result = result.plus(VarPolynomial.toVarPolynomial(monomial, xs));
            // beware of these garbage collector invocations ...
            // ... this conversion method won't last forever, though.
        }
        return result;
    }

    /**
     * Creates a Pair of a Polynomial and a Set of its variables which is
     * equivalent to varPoly.
     * @param varPoly the VarPolynomial to be converted
     * @return the Pair of a Polynomial and its variables, equivalent to varPoly
     */
    public static Pair<Polynomial, Set<String>> toPolynomial(final VarPolynomial varPoly) {

        final Set<String> variables = new LinkedHashSet<String>();
        // the set of variables of varPoly, 2nd component of result

        final Polynomial resultPoly = Polynomial.createConstant(0);
        // the Polynomial which is supposed to become the 1st component of result

        // derive the Strings of the variables from the keys of the varPoly
        // and add them to the set of variables
        for (final IndefinitePart key : varPoly.varMonomials.keySet()) {
            for (final String variable : key.getExponents().keySet()) {
                variables.add(variable);
            }
        }

        // compute the Polynomial (sum of Monomials)
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : varPoly.varMonomials.entrySet()) {
            resultPoly.addAll(VarPolynomial.times(entry.getKey(), entry.getValue()));
        }

        return new Pair<Polynomial, Set<String>>(resultPoly, variables);
    }

    /**
     * Converts a Map of Polynomials to their corresponding variables to an
     * equivalent Set of VarPolynomials.
     * @param polyMap a Map from Polynomials to their variables
     * @return a Set of the corresponding VarPolynomials
     */
    public static Set<VarPolynomial> toVarPolynomials(final Map<Polynomial, Set<String>> polyMap) {
        final Set<VarPolynomial> result = new LinkedHashSet<VarPolynomial>(); // to be returned

        for (final Map.Entry<Polynomial, Set<String>> entry : polyMap.entrySet()) {
            result.add(VarPolynomial.toVarPolynomial(entry.getKey(), entry.getValue()));
        }

        return result;
    }

    /**
     * Converts a Set of VarPolynomials to a Map of Polynomials to their
     * corresponding variables. Prerequisite: Two VarPolynomials that have
     * equivalent Polynomials must also have the same sets of variables,
     * otherwise the result of the conversion will not be equivalent to
     * varPolySet (the returned Map must be well-defined).
     * @param varPolySet the Set of VarPolynomials to be converted
     * @return the conversion result: a Map from the resulting Polynomials to
     * their variables
     */
    public static Map<Polynomial, Set<String>> toPolynomials(final Set<VarPolynomial> varPolySet) {
        Pair<Polynomial, Set<String>> currentPolyPair; // temporary variable for the currentPolynomial and its variables
        final Map<Polynomial, Set<String>> result = new LinkedHashMap<Polynomial, Set<String>>(); // to be returned

        for (final VarPolynomial varPoly : varPolySet) {
            currentPolyPair = VarPolynomial.toPolynomial(varPoly);
            result.put(currentPolyPair.getKey(), currentPolyPair.getValue());
        }

        return result;
    }

    /**
     * Multiplies an IndefinitePart and a SimplePolynomial, thus creating a
     * Polynomial whose Monomials contain both variables and indefinite
     * coefficients as "variables". Needed by this.toPolynomial(...).
     * @param indefinitePart the IndefinitePart (usually of variables) to be
     * multiplied to simplePoly
     * @param simplePoly the SimplePolynomial to be multiplied to SimplePoly
     * @return the Polynomial which represents the product of indefinitePart and
     * simplePoly
     */
    private static Polynomial times(final IndefinitePart indefinitePart, final SimplePolynomial simplePoly) {
        final Polynomial result = Polynomial.createConstant(0); // to be returned
        IndefinitePart currentIndefinitePart; // temporary variable for the resulting indefinitePart
        Monomial currentMonomial; // temporary variable for the resulting Monomials

        for (final Map.Entry<IndefinitePart, BigInteger> entry : simplePoly.getSimpleMonomials().entrySet()) {
            final IndefinitePart indefiniteCoeffs = entry.getKey();
            currentIndefinitePart = indefinitePart.times(indefiniteCoeffs);
            if (!BigInteger.valueOf(entry.getValue().intValue()).equals(entry.getValue())) {
                return null;
            }
            currentMonomial =
                Monomial.create(
                    entry.getValue().intValue(),
                    new TreeMap<String, Integer>(currentIndefinitePart.getExponents()));
            result.add(currentMonomial);
        }

        return result;
    }

    /**
     * Converts a Monomial, given its variables, to a VarPolynomial. Needed by
     * this.toVarPolynomial(...).
     * @param monomial the Monomial which is supposed to be added to varPoly
     * @param xs Set of the actual variables of monomial (as opposed to its
     * coefficients)
     */
    private static VarPolynomial toVarPolynomial(final Monomial monomial, final Set<String> xs) {
        final Map<IndefinitePart, SimplePolynomial> result = new LinkedHashMap<IndefinitePart, SimplePolynomial>();
        // to be returned (as VarPolynomial)

        // pair of variable part and coefficient part of the monomial
        Pair<Polynomial, Polynomial> split;

        // components of split
        Polynomial variablePartPoly;
        Polynomial coefficientPartPoly;

        // representations of variablePartOfMonomial and
        // coefficientPartOfMonomial in the new formats
        IndefinitePart variableIndefinitePart;
        SimplePolynomial coefficientSimplePolynomial;

        split = monomial.splitCoefficient(xs);
        variablePartPoly = split.getKey();
        coefficientPartPoly = split.getValue();

        variableIndefinitePart = IndefinitePart.toIndefinitePart(variablePartPoly);
        coefficientSimplePolynomial = SimplePolynomial.toSimplePolynomial(coefficientPartPoly);

        result.put(variableIndefinitePart, coefficientSimplePolynomial);
        return new VarPolynomial(result);
    }

    /**
     * Returns the SimplePolynomial which is the factor of ip in this.
     * @param ip the IndefinitePart whose coefficient polynomial is desired
     * @return the SimplePolynomial which is the coefficient of ip or null if ip
     * does not occur in the variable part of this
     */
    public SimplePolynomial getCoefficientPoly(final IndefinitePart ip) {
        return this.varMonomials.get(ip);
    }

    /**
     * Returns the sum of those simple polynomials that are some coefficient of
     * a indefinite part containing x
     * @param x
     * @return
     */
    public SimplePolynomial getSumOfCoefficientPolys(final String x) {
        SimplePolynomial p = SimplePolynomial.ZERO;
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : this.varMonomials.entrySet()) {
            final IndefinitePart ip = entry.getKey();
            if (ip.contains(x)) {
                p = p.plus(entry.getValue());
            }
        }
        return p;
    }

    /**
     * Returns the list of those simple polynomials that are some coefficient of
     * a indefinite part containing x
     * @param x
     * @return
     */
    public List<SimplePolynomial> getListOfCoefficientPolys(final String x) {
        final List<SimplePolynomial> list = new ArrayList<SimplePolynomial>(3);
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : this.varMonomials.entrySet()) {
            final IndefinitePart ip = entry.getKey();
            if (ip.contains(x)) {
                list.add(entry.getValue());
            }
        }
        return list;
    }

    /**
     * Returns the SimplePolynomial which is the factor of x in this, provided
     * that x occurs "alone" in an IndefinitePart of this.
     * @param x we want its factor in this
     * @return the factor of x in this or null if x does not occur without any
     * other variable factors or at power != 1 in some monomial of this
     */
    public SimplePolynomial getCoefficientPoly(final String x) {
        return this.varMonomials.get(new IndefinitePart(x));
    }

    /**
     * Needed for strong monotonicity.
     * @param x
     * @return the sum of all coeff polys of an IndefinitePart of proper
     * variables where x and only x occurs at least at power 1
     */
    public SimplePolynomial getStrongMonotonicitySum(final String x) {
        SimplePolynomial result = SimplePolynomial.ZERO;
        final Set<String> xSingleton = Collections.singleton(x);
        for (final Entry<IndefinitePart, SimplePolynomial> e : this.varMonomials.entrySet()) {
            if (e.getKey().getExponents().keySet().equals(xSingleton)) {
                result = result.plus(e.getValue());
            }
        }
        return result;
    }

    /**
     * @return the degree of the polynomial, i.e., the maximal degree of some
     * monomial (where opposed to an algebraic point of view, the degree of ZERO
     * is 0 and not -\infty)
     */
    public int getDegree() {
        int res = 0;
        for (final Entry<IndefinitePart, SimplePolynomial> monomial : this.varMonomials.entrySet()) {
            final int exp = monomial.getKey().getDegree();
            if (exp > res) {
                res = exp;
            }
        }
        return res;
    }

    /**
     * The degree of variable x in p is the biggest exponent of x occurring in p
     * with non-zero coefficient. If a variable does not occur, then the degree
     * of x is 0.
     * @param variable some variable
     * @return int
     */
    public int getDegreeOfVariable(final String variable) {
        int res = 0;
        for (final IndefinitePart monomial : this.varMonomials.keySet()) {
            if (monomial.contains(variable)) {
                final int exp = monomial.getExponent(variable);
                res = (res > exp) ? res : exp;
            }
        }
        return res;
    }

    /**
     * Adds a VarPolynomial to this and returns the result.
     * @param varPoly the VarPolynomial to be added to this
     * @return the sum of the two VarPolynomials
     */
    public VarPolynomial plus(final VarPolynomial varPoly) {
        final Map<IndefinitePart, SimplePolynomial> result = new LinkedHashMap<IndefinitePart, SimplePolynomial>();
        // to be returned (as VarPolynomial)

        SimplePolynomial sum; // temporary variable that contains the sum of two SimplePolynomials

        // First consider all mappings of IndefiniteParts to SimplePolynomials of this ...
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : this.varMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey(); // temp. variable for the 1st component of entry

            // If a key occurs in both VarPolynomials, we do the addition.
            final SimplePolynomial currentSimplePoly = varPoly.varMonomials.get(key);
            if (currentSimplePoly != null) {
                sum = entry.getValue().plus(currentSimplePoly);
                if (!sum.isZero()) { // adding 0 is pointless
                    result.put(key, sum);
                }
            } else { // just include the old mapping of this
                result.put(key, entry.getValue());
            }
        }

        // ... then the ones in varPoly which have not been considered so far.
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : varPoly.varMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey(); // temp. variable for the 1st component of entry
            if (!this.varMonomials.containsKey(key)) {
                result.put(key, entry.getValue());
            }
        }

        return new VarPolynomial(result);
    }

    /**
     * Adds several VarPolynomial and returns the result.
     * @param varPolys the VarPolynomials to be added
     * @return the sum of the two VarPolynomials
     */
    public static VarPolynomial plus(final List<VarPolynomial> varPolys) {
        final Map<IndefinitePart, SimplePolynomial> result = new LinkedHashMap<IndefinitePart, SimplePolynomial>();
        // to be returned (as VarPolynomial)

        final Map<IndefinitePart, List<SimplePolynomial>> addends =
            new LinkedHashMap<IndefinitePart, List<SimplePolynomial>>();

        // First consider all mappings of IndefiniteParts to SimplePolynomials of this ...
        for (final VarPolynomial varPoly : varPolys) {

            // Gather all addends...
            for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : varPoly.varMonomials.entrySet()) {
                List<SimplePolynomial> addend;
                addend = addends.get(entry.getKey());
                if (addend != null) {
                    addend.add(entry.getValue());
                } else {
                    final List<SimplePolynomial> newList = new ArrayList<SimplePolynomial>();
                    newList.add(entry.getValue());
                    addends.put(entry.getKey(), newList);
                }
            }

        }

        for (final Map.Entry<IndefinitePart, List<SimplePolynomial>> entry : addends.entrySet()) {
            // ... and add them
            final SimplePolynomial factorSum = SimplePolynomial.plus(entry.getValue());
            if (!factorSum.isZero()) {
                result.put(entry.getKey(), factorSum);
            }
        }

        return new VarPolynomial(result);
    }

    /**
     * Multiplies a varPoly to this and returns the result.
     * @param varPoly the varPoly to be multiplied to this
     * @return the product of the two VarPolynomials
     */
    // TODO: use abortable function in more methods
    public VarPolynomial times(final VarPolynomial varPoly) {
        VarPolynomial result = null;
        try {
            result = this.times(varPoly, AbortionFactory.create());
        } catch (final AbortionException e) {
            throw new RuntimeException(e);
        }
        return result;
    }

    public VarPolynomial times(final VarPolynomial varPoly, final Abortion aborter) throws AbortionException {
        final Map<IndefinitePart, SimplePolynomial> result = new LinkedHashMap<IndefinitePart, SimplePolynomial>();
        // to be returned (as VarPolynomial)

        IndefinitePart newKey; // temporary variable needed for the product of two IndefiniteParts
        SimplePolynomial newValue; // temporary variable needed for the product of two SimplePolynomials

        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry1 : this.varMonomials.entrySet()) {
            final IndefinitePart key1 = entry1.getKey();
            final SimplePolynomial value1 = entry1.getValue();
            for (final Map.Entry<IndefinitePart, SimplePolynomial> entry2 : varPoly.varMonomials.entrySet()) {
                aborter.checkAbortion();
                newKey = key1.times(entry2.getKey());
                newValue = value1.times(entry2.getValue(), aborter);
                // by induction, newValue cannot represent a zero SimplePolynomial because otherwise,
                // one of the previous SimplePolynomials would have been zero,
                // which does (should) not happen (contradiction to the minimality
                // of representation of VarPolynomials).

                final SimplePolynomial oldValue = result.get(newKey);
                if (oldValue == null) {
                    result.put(newKey, newValue);
                } else {
                    newValue = newValue.plus(oldValue);
                    if (newValue.isZero()) {
                        result.remove(newKey);
                    } else {
                        result.put(newKey, newValue);
                    }
                }
            }
        }
        aborter.checkAbortion();
        return new VarPolynomial(result);
    }

    /**
     * Multiplies a SimplePolynomial to this and returns the result.
     * @param sp will be multiplied to this
     * @return the product of this and sp
     */
    public VarPolynomial times(final SimplePolynomial sp) {
        if (sp.equals(SimplePolynomial.ZERO)) {
            return VarPolynomial.ZERO;
        }
        if (sp.equals(SimplePolynomial.ONE)) {
            return this;
        }
        final Map<IndefinitePart, SimplePolynomial> result = new LinkedHashMap<IndefinitePart, SimplePolynomial>();
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : this.varMonomials.entrySet()) {
            result.put(entry.getKey(), sp.times(entry.getValue()));
        }
        return VarPolynomial.create(result);
    }

    /**
     * @return a negated version of this
     */
    public VarPolynomial negate() {
        final Map<IndefinitePart, SimplePolynomial> result =
            new LinkedHashMap<IndefinitePart, SimplePolynomial>(this.varMonomials.size());
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : this.varMonomials.entrySet()) {
            result.put(entry.getKey(), entry.getValue().negate());
        }
        return VarPolynomial.create(result);
    }

    /**
     * @param subtrahend to be subtracted from this
     * @return this - subtrahend
     */
    public VarPolynomial minus(final VarPolynomial subtrahend) {
        final Map<IndefinitePart, SimplePolynomial> result = new LinkedHashMap<IndefinitePart, SimplePolynomial>();
        // to be returned (as VarPolynomial)

        SimplePolynomial difference;
        // temporary variable that contains the difference of two SimplePolynomials

        // First consider all mappings of IndefiniteParts to SimplePolynomials of this ...
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : this.varMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey(); // temp. variable for the 1st component of entry

            // If a key occurs in both VarPolynomials, we do the subtraction.
            final SimplePolynomial currentSimplePoly = subtrahend.varMonomials.get(key);
            if (currentSimplePoly != null) {
                difference = entry.getValue().minus(currentSimplePoly);
                if (!difference.isZero()) { // adding 0 is pointless
                    result.put(key, difference);
                }
            } else { // just include the old mapping of this
                result.put(key, entry.getValue());
            }
        }

        // ... then the ones in subtrahend which have not been considered so far.
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : subtrahend.varMonomials.entrySet()) {
            final IndefinitePart key = entry.getKey(); // temp. variable for the 1st component of entry
            if (!this.varMonomials.containsKey(key)) {
                result.put(key, entry.getValue().negate());
            }
        }

        return VarPolynomial.create(result);
    }

    /**
     * Returns the VarPolynomial in which all indefinite coefficients are
     * replaced by <code>value</code>.
     * @param value to be assigned to each indefinite coefficient of this
     * @return the SimplePolynomial in which all indefinite coefficients have
     * been replaced by <code>value</code>.
     */
    public VarPolynomial setAllIndefiniteCoeffsTo(final BigInteger value) {
        Map<IndefinitePart, SimplePolynomial> polyMap;
        polyMap = new LinkedHashMap<IndefinitePart, SimplePolynomial>();
        for (final Map.Entry<IndefinitePart, SimplePolynomial> e : this.varMonomials.entrySet()) {
            SimplePolynomial specializedFactor;
            specializedFactor = e.getValue().setAllIndefinitesTo(value);
            if (!specializedFactor.isZero()) {
                polyMap.put(e.getKey(), specializedFactor);
            }
        }
        return VarPolynomial.create(polyMap);
    }

    /**
     * Computes a version of this in which the coefficients of this that occur
     * in the key set of values are replaced by the corresponding numerical
     * values indicated by values.
     * @param values coefficient-to-value mapping for known coefficient values
     * @return the specialized VarPolynomial
     */
    public VarPolynomial specialize(final Map<String, BigInteger> values) {
        final Map<IndefinitePart, SimplePolynomial> result = new LinkedHashMap<IndefinitePart, SimplePolynomial>();
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : this.varMonomials.entrySet()) {
            SimplePolynomial specializedFactor;
            specializedFactor = entry.getValue().specialize(values);
            if (!specializedFactor.equals(SimplePolynomial.ZERO)) {
                result.put(entry.getKey(), specializedFactor);
            }
        }
        return VarPolynomial.create(result);
    }

    /**
     * @param x - a variable
     * @return the first derivative of this with respect to x
     */
    public VarPolynomial deriveWRT(final String x) {
        final Map<IndefinitePart, SimplePolynomial> result = new LinkedHashMap<IndefinitePart, SimplePolynomial>();
        for (final Entry<IndefinitePart, SimplePolynomial> entry : this.varMonomials.entrySet()) {
            final IndefinitePart iPart = entry.getKey();
            final Pair<Integer, IndefinitePart> iPartDerivative = iPart.deriveWRT(x);
            if (iPartDerivative.x != 0) {
                final BigInteger oldExponent = BigInteger.valueOf(iPartDerivative.x);
                final SimplePolynomial newCoeffPoly = entry.getValue().times(oldExponent);
                // note that iPartDerivative.y cannot occur in result yet;
                // derivation restricted to polynomials which have a non-zero
                // derivative should be injective
                result.put(iPartDerivative.y, newCoeffPoly);
            }
        }
        return VarPolynomial.create(result);
    }

    /**
     * Returns this<sup>exponent</sup>.
     * @param exponent non-negative exponent
     * @param aborter stops the operation if the result is not needed anymore
     * @return this<sup>exponent</sup>
     * @throws AbortionException if the aborter asks for it
     */
    public VarPolynomial power(int exponent, final Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert (exponent >= 0);
        }
        if (exponent == 0) {
            return VarPolynomial.ONE;
        } else if (exponent == 1) {
            return this;
        } else {
            VarPolynomial result = VarPolynomial.ONE;
            VarPolynomial tmp = this;
            while (exponent > 0) {
                if (exponent % 2 == 1) {
                    result = result.times(tmp, aborter);
                }
                exponent /= 2;
                if (exponent > 0) {
                    tmp = tmp.times(tmp, aborter);
                } else {
                    break; // somewhat ugly, but slightly more efficient
                           // (saves the last check of the loop cond.)
                }
            }
            return result;
        }
    }

    /**
     * Apply substitution to this. substitution's key variables may also occur
     * inside the values. Note that only real variables are substituted, not
     * indefinite coefficients.
     * @param substitution to be performed on this
     * @return substitution(this)
     */
    // TODO: use abortable function in more methods
    public VarPolynomial substituteVariables(final Map<String, VarPolynomial> substitution) {
        VarPolynomial result = null;
        try {
            result = this.substituteVariables(substitution, AbortionFactory.create());
        } catch (final AbortionException e) {
            throw new RuntimeException(e);
        }
        return result;
    }

    /**
     * Applies a substitution, i.e., the variables are replaced by polynomial according to
     * the given map.
     * @param substitution maps string to polynomials
     * @param aborter some aborter
     * @return another polynomial
     * @throws AbortionException can be aborted
     */
    public VarPolynomial substituteVariables(final Map<String, VarPolynomial> substitution, final Abortion aborter)
        throws AbortionException
    {
        VarPolynomial result;
        result = VarPolynomial.ZERO;

        for (final Map.Entry<IndefinitePart, SimplePolynomial> monomEntry : this.varMonomials.entrySet()) {
            aborter.checkAbortion();
            final IndefinitePart keyIP = monomEntry.getKey();
            VarPolynomial substitutePoly = VarPolynomial.ONE;
            Set<String> substitutedVars;
            substitutedVars = new LinkedHashSet<String>();
            // - now iterate over all the variables in substitution's keyset
            for (final Map.Entry<String, VarPolynomial> substEntry : substitution.entrySet()) {
                final String substKey = substEntry.getKey();
                // ** multiply the resulting polys at the power at which their
                //    key used to occur in keyIP (if > 0)
                //    and remember the key to remove it later
                final int exponent = keyIP.getExponent(substKey);
                if (exponent > 0) {
                    substitutePoly = substitutePoly.times(substEntry.getValue().power(exponent, aborter), aborter);
                    substitutedVars.add(substKey);
                }
                aborter.checkAbortion();
            }
            // - remove these vars from keyIP
            IndefinitePart newIP;
            newIP = keyIP.removeIndefinites(substitutedVars);
            // - multiply the resulting poly to newIP*e.getValue()
            Map<IndefinitePart, SimplePolynomial> newExp;
            newExp = Collections.singletonMap(newIP, monomEntry.getValue());
            final VarPolynomial newPoly = new VarPolynomial(newExp);
            aborter.checkAbortion();
            substitutePoly = substitutePoly.times(newPoly, aborter);
            aborter.checkAbortion();
            // - add substitutePoly to result
            result = result.plus(substitutePoly);
        }
        return result;
    }

    /**
     * Prerequisite: Hook variables shared by several values of substitution
     * must point to the same value.
     * @param substitution
     * @return
     */
    public OpVarPolynomial substituteVarsWithOpVPs(final Map<String, OpVarPolynomial> substitution) {
        final Set<String> vars = this.getVariables();
        final Map<String, VarPolynomial> subst = new LinkedHashMap<String, VarPolynomial>(substitution.size());
        final Map<String, OpApp> varsToOpArgs = new LinkedHashMap<String, OpApp>();
        for (final Entry<String, OpVarPolynomial> e : substitution.entrySet()) {
            final String toBeSubstituted = e.getKey();

            // do not regard irrelevant vars
            if (vars.contains(toBeSubstituted)) {
                final OpVarPolynomial ovp = e.getValue();
                subst.put(toBeSubstituted, ovp.getHookPoly());
                if (Globals.useAssertions) {
                    for (final Entry<String, OpApp> hookVarToArg : ovp.getVarsToOpArgs().entrySet()) {
                        final String hookVar = hookVarToArg.getKey();
                        final OpApp varsToOpArgsValue = varsToOpArgs.get(hookVar);
                        if (varsToOpArgsValue != null) {
                            assert varsToOpArgsValue.equals(hookVarToArg.getValue());
                        }
                    }
                }
                varsToOpArgs.putAll(ovp.getVarsToOpArgs());
            }
        }
        final VarPolynomial substitutedHook = this.substituteVariables(subst);

        // the next steps are necessary e.g. because of the following example:
        // this = x1 - x2, substitution = [x1/max(x3,x4), x2/max(x3,x4)]
        final Set<String> resultingVars = substitutedHook.getVariables();
        varsToOpArgs.keySet().retainAll(resultingVars);

        return OpVarPolynomial.create(substitutedHook, varsToOpArgs);
    }

    /**
     * Getter for this.varMonomials.
     * @return the mapping that effectively constitutes the addends of this
     */
    public ImmutableMap<IndefinitePart, SimplePolynomial> getVarMonomials() {
        return this.varMonomials;
    }

    /**
     * Evaluate this. Note that only real variables are evaluated, not
     * indefinite coefficients.
     * @param valuation to be performed on this, must have all variables of this
     * in its keySet
     * @return valuation(this)
     */
    public SimplePolynomial evaluate(final Map<String, Integer> valuation) {
        if (Globals.useAssertions) {
            assert valuation.keySet().containsAll(this.getVariables());
        }

        // TODO more direct implementation
        Map<String, VarPolynomial> substitution;
        substitution = new LinkedHashMap<String, VarPolynomial>(valuation.size());
        for (final Map.Entry<String, Integer> e : valuation.entrySet()) {
            substitution.put(e.getKey(), VarPolynomial.create(e.getValue()));
        }
        final VarPolynomial res = this.substituteVariables(substitution);
        if (Globals.useAssertions) {
            assert res.getVariables().isEmpty();
        }
        return res.getConstantPart();
    }

    /**
     * Normalizes this modulo n. Apply only if this does not contain any
     * indefinite coefficients in the factors, i.e., if factor.isConstant()
     * holds for all factors in this. Most useful e.g. for Semantic Labeling,
     * not needed for POLO.
     * @param n all factors of this will be normalized modulo n, e.g., (2x + 15y
     * + 5).normalizeModulo(3) = 2x + 2
     * @return a normalized version of this modulo n
     */
    public VarPolynomial normalizeModulo(final int n) {
        if (Globals.useAssertions) {
            for (final SimplePolynomial factor : this.varMonomials.values()) {
                assert factor.isConstant();
            }
        }
        final BigInteger bigN = BigInteger.valueOf(n);
        Map<IndefinitePart, SimplePolynomial> result;
        result = new LinkedHashMap<IndefinitePart, SimplePolynomial>(this.varMonomials.size());
        for (final Entry<IndefinitePart, SimplePolynomial> e : this.varMonomials.entrySet()) {
            final SimplePolynomial oldFactorPoly = e.getValue();
            final BigInteger newFactor = oldFactorPoly.getNumericalAddend().remainder(bigN);
            if (newFactor.signum() != 0) { // do not include zero addend
                final SimplePolynomial newFactorPoly = SimplePolynomial.create(newFactor);
                final IndefinitePart key = e.getKey();
                result.put(key, newFactorPoly);
            }
        }
        return new VarPolynomial(result);
    }

    /**
     * @return whether this only contains monomials with a degree of at most 1
     *  (where we disregard the coefficient polynomials)
     */
    public boolean isLinear() {
        for (final IndefinitePart iPart : this.varMonomials.keySet()) {
            if (!iPart.isLinear()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return whether this is a concrete polynomial, i.e., all coefficients of
     * this are actual numbers
     */
    public boolean isConcrete() {
        for (final SimplePolynomial sp : this.varMonomials.values()) {
            if (!sp.isConstant()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return whether this is just a constant number
     */
    public boolean isConstant() {
        final int size = this.varMonomials.size();
        switch (size) {
        case 0: // the empty varpoly is 0, i.e., a constant
            return true;
        case 1: // just one addend, might be a constant
            SimplePolynomial factorOfOne;
            factorOfOne = this.varMonomials.get(IndefinitePart.ONE);
            if (factorOfOne == null) { // no constant addend
                return false;
            }
            // okay, now check whether factorOfOne is a number
            return factorOfOne.isConstant();
        default: // too many addends
            return false;
        }
    }

    /**
     * @return the SimplePolynomial that is a factor of IndefinitePart.ONE in
     * this
     */
    public SimplePolynomial getConstantPart() {
        SimplePolynomial res = this.varMonomials.get(IndefinitePart.ONE);
        if (res == null) {
            res = SimplePolynomial.ZERO;
        }
        return res;
    }

    /**
     * @return the SimplePolynomials that are coefficients of variables of this
     */
    public Set<SimplePolynomial> getCoefficientsOfVariables() {
        final Set<SimplePolynomial> coeffs = new LinkedHashSet<SimplePolynomial>(this.varMonomials.size());
        for (final Map.Entry<IndefinitePart, SimplePolynomial> entry : this.varMonomials.entrySet()) {
            if (!entry.getKey().isEmpty()) {
                coeffs.add(entry.getValue());
            }
        }
        return coeffs;
    }

    /**
     * @return an iterator over all coefficients without putting them into
     *  a new set.
     */
    public Iterable<SimplePolynomial> getAllCoefficients() {
        return new Iterable<SimplePolynomial>() {

            @Override
            public Iterator<SimplePolynomial> iterator() {
                final Iterator<SimplePolynomial> internalIterator = VarPolynomial.this.varMonomials.values().iterator();
                return new Iterator<SimplePolynomial>() {

                    @Override
                    public boolean hasNext() {
                        return internalIterator.hasNext();
                    }

                    @Override
                    public SimplePolynomial next() {
                        return internalIterator.next();
                    }

                    @Override
                    public void remove() {
                        throw new UnsupportedOperationException();
                    }

                };
            }
        };
    }

    /**
     * @return whether this is of form 1*x^1 for some variable x
     */
    public boolean isVariable() {
        if (this.varMonomials.size() == 1) {
            Map.Entry<IndefinitePart, SimplePolynomial> theMonomial;
            theMonomial = this.varMonomials.entrySet().iterator().next();
            if (theMonomial.getKey().isIndefinite() && theMonomial.getValue().equals(SimplePolynomial.ONE)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return all proper variables of this
     */
    public Set<String> getVariables() {
        Set<String> vars;
        vars = new LinkedHashSet<String>();
        for (final IndefinitePart ip : this.varMonomials.keySet()) {
            vars.addAll(ip.getIndefinites());
        }
        return vars;
    }

    /**
     * @return all indefinite coefficients as found in the coefficient
     * polynomials of this
     */
    public Set<String> getCoefficients() {
        Set<String> result;
        result = new LinkedHashSet<String>();
        for (final SimplePolynomial sp : this.varMonomials.values()) {
            result.addAll(sp.getIndefinites());
        }
        return result;
    }

    /**
     * @return the number of addends (on top level) of this
     */
    public int numberOfAddends() {
        return this.varMonomials.size();
    }

    /**
     * @return whether all addends of this have SimplePolynomials as factors
     * that only have positive factors (note: this property also holds if
     * this.equals(ZERO), i.e., there are no addends whatsoever)
     */
    public boolean allPositive() {
        for (final SimplePolynomial sp : this.varMonomials.values()) {
            if (!sp.allPositive()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return whether all addends of this have SimplePolynomials as factors
     * that only have negative factors (note: this property also holds if
     * this.equals(ZERO), i.e., there are no addends whatsoever)
     */
    public boolean allNegative() {
        for (final SimplePolynomial sp : this.varMonomials.values()) {
            if (!sp.allNegative()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Assumes all indefinite coefficients to be instantiated by 0.
     * @param x
     * @return whether this is strongly monotonic in x on the naturals
     * (sufficient criterion only, false negatives are possible, e.g., 2*x^2 -
     * x) since we test whether all coefficients of any x^i are non-negative and
     * at least one of them is positive
     */
    public boolean isStronglyMonotonicIn(final String x) {
        boolean posCoeffFound = false;
        for (final Entry<IndefinitePart, SimplePolynomial> varMonomial : this.varMonomials.entrySet()) {
            final IndefinitePart ip = varMonomial.getKey();
            if (ip.containsExactly(x)) {
                final BigInteger constant = varMonomial.getValue().getNumericalAddend();
                switch (constant.signum()) {
                case 1:
                    posCoeffFound = true;
                    break;
                case -1:
                    return false;
                default:
                    assert false; // should not occur by construction
                }
            }
        }
        return posCoeffFound;
    }

    /**
     * Assumes all indefinite coefficients to be instantiated by 0.
     *
     * @return in which variables this is strongly monotonic (sufficient
     * criterion only, false negatives are possible, e.g., 2*x^2 - x) since we
     * test whether all coefficients of any x^i are non-negative and at least
     * one of them is positive; may be modified
     */
    public Set<String> getStronglyMonotonicVars() {
        // monotonic until shown otherwise
        final Set<String> vars = this.getVariables();

        for (final Entry<IndefinitePart, SimplePolynomial> varMonomial : this.varMonomials.entrySet()) {
            final IndefinitePart ip = varMonomial.getKey();
            final String indef = ip.getTheOnlyIndefinite();
            if (indef != null) {
                final BigInteger n = varMonomial.getValue().getNumericalAddend();
                if (n.signum() < 0) {
                    vars.remove(indef);
                }
                // n.signum() != 0 by construction
            }
        }
        return vars;
    }

    public boolean containsVariable(final String x) {
        for (final IndefinitePart ip : this.varMonomials.keySet()) {
            if (ip.contains(x)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Compares two VarPolynomials lexicographically. In ascending order wrt the
     * natural order on IndefiniteParts, we check which of the two
     * IndefiniteParts is the greater one; if they are equal, we check which of
     * the corresponding factors is bigger; if they are equal as well, we
     * proceed to the next IndefinitePart if existant. In the end, we check
     * whether one of the VarPolynomials is a proper prefix of the other. If
     * not, they must be equal. E.g.: a * x*y < b * x*y < a * x*z < a * x*z + 4
     * * x^2*z^2
     * @see java.lang.Comparable#compareTo(VarPolynomial)
     * @param other
     * @return
     */
    @Override
    public int compareTo(final VarPolynomial other) {
        SortedMap<IndefinitePart, SimplePolynomial> m1, m2;
        m1 = new TreeMap<IndefinitePart, SimplePolynomial>(this.varMonomials);
        m2 = new TreeMap<IndefinitePart, SimplePolynomial>(other.varMonomials);

        Iterator<Map.Entry<IndefinitePart, SimplePolynomial>> iter1, iter2;
        iter1 = m1.entrySet().iterator();
        iter2 = m2.entrySet().iterator();

        Map.Entry<IndefinitePart, SimplePolynomial> e1, e2;
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
                int factorDifference;
                factorDifference = e1.getValue().compareTo(e2.getValue());
                if (factorDifference != 0) {
                    return factorDifference;
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

    /**
     * Rewrites this polynomial into a term.
     * @param predefined fill in some predefined map
     * @return a term
     */
    public TRSTerm toTerm(final IDPPredefinedMap predefined) {
        if (this.equals(VarPolynomial.ZERO)) {
            return predefined.getIntTerm(BigIntImmutable.ZERO, DomainFactory.INTEGERS);
        }

        TRSTerm result = null;
        for (final Entry<IndefinitePart, SimplePolynomial> e : this.varMonomials.entrySet()) {
            final IndefinitePart indef = e.getKey();
            final SimplePolynomial simple = e.getValue();

            TRSTerm current;
            if (simple.equals(SimplePolynomial.ONE)) {
                current = indef.toTerm(predefined);
            } else {
                current = simple.toTerm(predefined);
                if (!indef.equals(IndefinitePart.ONE)) {
                    current =
                        TRSTerm.createFunctionApplication(
                            predefined.getSym(Func.Mul, DomainFactory.INTEGERS),
                            current,
                            indef.toTerm(predefined));
                }
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
        assert result != null : "VarPolynomial with empty monomial-map, but != 0.";

        return result;
    }

    /**
     * Returns a SMTLIBInt-Representation of this.
     * @return SMTLIBIntValue
     */
    public SMTLIBIntValue toSMTLIB() {
        if (this.equals(VarPolynomial.ZERO)) {
            return SMTLIBIntConstant.create(BigInteger.ZERO);
        } else {
            final LinkedList<SMTLIBIntValue> valueList = new LinkedList<>();

            for (final Entry<IndefinitePart, SimplePolynomial> e : this.varMonomials.entrySet()) {
                final SMTLIBIntValue keyValue = e.getKey().toSMTLIB();
                final SMTLIBIntValue valueValue = e.getValue().toSMTLIB();

                final LinkedList<SMTLIBIntValue> toMult = new LinkedList<>();
                toMult.add(keyValue);
                toMult.add(valueValue);
                final SMTLIBIntValue toAdd = SMTLIBIntMult.create(toMult);
                valueList.add(toAdd);
            }

            return SMTLIBIntPlus.create(valueList);
        }
    }

    /**
     * Rewrites this polynomial into a term. This implementation uses the
     * default predefined map.
     * @return a term
     */
    public TRSTerm toTerm() {
        return this.toTerm(IDPPredefinedMap.DEFAULT_MAP);
    }

    @Override
    public String export(final Export_Util eu) {
        if (this.varMonomials.isEmpty()) {
            return "0";
        }
        StringBuilder buffer;
        buffer = new StringBuilder(20 * this.varMonomials.size());
        Iterator<Map.Entry<IndefinitePart, SimplePolynomial>> iter;
        SortedMap<IndefinitePart, SimplePolynomial> m;
        m = new TreeMap<IndefinitePart, SimplePolynomial>(this.varMonomials);
        iter = m.entrySet().iterator();

        boolean first = true;
        while (iter.hasNext()) {
            Map.Entry<IndefinitePart, SimplePolynomial> entry;
            entry = iter.next();
            final IndefinitePart varPart = entry.getKey();
            final SimplePolynomial coeffPoly = entry.getValue();
            final boolean varPartIsOne = varPart.equals(IndefinitePart.ONE);
            if (varPartIsOne || (!coeffPoly.equals(SimplePolynomial.ONE))) {
                final boolean coeffIsSum = coeffPoly.numberOfAddends() > 1;
                final boolean negativeConstant = !coeffIsSum && coeffPoly.allNegative() && !coeffPoly.isZero();
                if (negativeConstant) {
                    final SimplePolynomial pos = coeffPoly.negate();
                    if (first) {
                        buffer.append("-");
                    } else {
                        buffer.append(" - ");
                    }
                    final boolean coeffIsOne = pos.equals(SimplePolynomial.ONE);
                    if (!coeffIsOne || varPartIsOne) {
                        buffer.append(pos.export(eu));
                    }
                    if (!varPartIsOne && !pos.equals(SimplePolynomial.ONE)) {
                        buffer.append(eu.multSign());
                    }
                } else {
                    if (!first) {
                        buffer.append(" + ");
                    }
                    if (coeffIsSum) {
                        buffer.append("(");
                    }
                    buffer.append(coeffPoly.export(eu));
                    if (coeffIsSum) {
                        buffer.append(")");
                    }
                    if (!varPartIsOne) {
                        buffer.append(eu.multSign());
                    }
                }
            } else {
                if (!first) {
                    buffer.append(" + ");
                }
            }
            if (!varPartIsOne) {
                buffer.append(varPart.export(eu));
            }
            first = false;
        }

        return buffer.toString();
    }

    /**
     * Like export(Export_Util), but varRepresentations indicates how certain
     * variables are supposed to be displayed
     * @param eu
     * @param varRepresentations
     * @return
     */
    public String export(final Export_Util eu, final Map<String, String> varRepresentations) {
        if (this.varMonomials.isEmpty()) {
            return "0";
        }
        StringBuilder buffer;
        buffer = new StringBuilder(20 * this.varMonomials.size());
        Iterator<Map.Entry<IndefinitePart, SimplePolynomial>> iter;
        SortedMap<IndefinitePart, SimplePolynomial> m;
        m = new TreeMap<IndefinitePart, SimplePolynomial>(this.varMonomials);
        iter = m.entrySet().iterator();

        boolean first = true;
        while (iter.hasNext()) {
            Map.Entry<IndefinitePart, SimplePolynomial> entry;
            entry = iter.next();
            final IndefinitePart varPart = entry.getKey();
            final SimplePolynomial coeffPoly = entry.getValue();
            final boolean varPartIsOne = varPart.equals(IndefinitePart.ONE);
            if (varPartIsOne || (!coeffPoly.equals(SimplePolynomial.ONE))) {
                final boolean coeffIsSum = coeffPoly.numberOfAddends() > 1;
                final boolean negativeConstant = !coeffIsSum && coeffPoly.allNegative() && !coeffPoly.isZero();
                if (negativeConstant) {
                    final SimplePolynomial pos = coeffPoly.negate();
                    if (first) {
                        buffer.append("-");
                    } else {
                        buffer.append(" - ");
                    }
                    final boolean coeffIsOne = pos.equals(SimplePolynomial.ONE);
                    if (!coeffIsOne || varPartIsOne) {
                        buffer.append(pos.export(eu, varRepresentations));
                    }
                    if (!varPartIsOne && !pos.equals(SimplePolynomial.ONE)) {
                        buffer.append(eu.multSign());
                    }
                } else {
                    if (!first) {
                        buffer.append(" + ");
                    }
                    if (coeffIsSum) {
                        buffer.append("(");
                    }
                    buffer.append(coeffPoly.export(eu, varRepresentations));
                    if (coeffIsSum) {
                        buffer.append(")");
                    }
                    if (!varPartIsOne) {
                        buffer.append(eu.multSign());
                    }
                }
            } else {
                if (!first) {
                    buffer.append(" + ");
                }
            }
            if (!varPartIsOne) {
                buffer.append(varPart.export(eu, varRepresentations));
            }
            first = false;
        }

        return buffer.toString();
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
        this.hashValue = this.varMonomials.hashCode();
        this.hashValid = true;
    }

    @Override
    public boolean equals(final Object o) {
        if (!(o instanceof VarPolynomial)) {
            return false;
        }
        final VarPolynomial varPoly = (VarPolynomial) o;

        // profit from our cached hash value
        if (varPoly.hashCode() != this.hashCode()) {
            return false;
        }
        return (varPoly.varMonomials.equals(this.varMonomials));
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.POLYNOMIAL.createElement(doc);
        for (final Map.Entry<IndefinitePart, SimplePolynomial> monomial : this.varMonomials.entrySet()) {
            final Element mon = XMLTag.MONOMIAL.createElement(doc);
            mon.appendChild(monomial.getValue().toDOM(doc, xmlMetaData));
            monomial.getKey().addToDOM(mon, doc);
            e.appendChild(mon);
        }
        return e;
    }

    public Element toRatCPF(final Document doc, final int denominator) {
        if (this.varMonomials.size() == 0) {
            return CPFTag.COEFFICIENT.create(doc, CPFTag.INTEGER.create(doc, 0));
        } else {
            if (this.varMonomials.size() == 1) {
                final Map.Entry<IndefinitePart, SimplePolynomial> monEntry =
                    this.varMonomials.entrySet().iterator().next();
                final IndefinitePart poloFactor = monEntry.getKey();
                final Element coeff = CPFTag.COEFFICIENT.create(doc, monEntry.getValue().toRatCPF(doc, denominator));
                if (poloFactor.getExponents().size() == 0) {
                    return coeff;
                } else {
                    throw new RuntimeException("problem in CPF export of VarPolynomial");
                }
            } else {
                throw new RuntimeException("problem in CPF export of VarPolynomial");
            }
        }
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element polynomial = CPFTag.POLYNOMIAL.createElement(doc);
        final Element sum = CPFTag.SUM.createElement(doc);
        if (this.varMonomials.size() == 0) {
            sum
                .appendChild(CPFTag.POLYNOMIAL.create(
                    doc,
                    CPFTag.COEFFICIENT.create(doc, CPFTag.INTEGER.create(doc, 0))));
        } else {
            for (final Map.Entry<IndefinitePart, SimplePolynomial> monEntry : this.varMonomials.entrySet()) {
                final Element polynomials = CPFTag.POLYNOMIAL.create(doc);
                final IndefinitePart poloFactor = monEntry.getKey();
                final Element coeff = CPFTag.COEFFICIENT.create(doc, monEntry.getValue().toCPF(doc));
                if (poloFactor.getExponents().size() == 0) {
                    polynomials.appendChild(coeff);
                } else {
                    final Element product = CPFTag.PRODUCT.create(doc, CPFTag.POLYNOMIAL.create(doc, coeff));
                    for (final Map.Entry<String, Integer> factor : poloFactor.getExponents().entrySet()) {
                        final String xName = factor.getKey();
                        final String xUnderscoreDeleted = xName.substring(2);
                        for (int i = 0; i < factor.getValue(); i++) {
                            product.appendChild(CPFTag.POLYNOMIAL.create(
                                doc,
                                CPFTag.VARIABLE.create(doc, xUnderscoreDeleted)));
                        }
                    }
                    polynomials.appendChild(product);
                }
                sum.appendChild(polynomials);
            }
        }
        polynomial.appendChild(sum);
        return polynomial;
    }
    
    /**
     * converts this var-poly to CPF-expression in LTS-style 
     * @param vars map from var-poly variables to CPF-expr variables
     */
    public Element toLtsCPF(final Document doc, Map<String,String> vars) {
        
        if (this.varMonomials.size() == 0) {
            return CPFTag.CONSTANT.create(doc, 0);
        } else {
            final Element sum = CPFTag.SUM.createElement(doc);
            for (final Map.Entry<IndefinitePart, SimplePolynomial> monEntry : this.varMonomials.entrySet()) {
                final Element coeff = monEntry.getValue().toLtsCPF(doc);
                final IndefinitePart poloFactor = monEntry.getKey();
                final Element polynomial = poloFactor.toCpfLTS(doc, coeff, vars);
                sum.appendChild(polynomial);
            }
            return sum;
        }
    }

    /**
     * Like <code>toDOM()</code>, but substitutes the variables contained in
     * <code>varRepresentations</code> by the associated XML subtrees.
     * @param xmlMetaData TODO
     */
    public Element toDOM2(
        final Document doc,
        final Map<String, Element> varRepresentations,
        final XMLMetaData xmlMetaData)
    {

        final Element polyTag = XMLTag.POLYNOMIAL.createElement(doc);
        for (final Map.Entry<IndefinitePart, SimplePolynomial> monomial : this.varMonomials.entrySet()) {
            final Element mon = XMLTag.MONOMIAL.createElement(doc);
            mon.appendChild(monomial.getValue().toDOM(doc, xmlMetaData));
            monomial.getKey().addToDOM(mon, doc, varRepresentations);
            polyTag.appendChild(mon);
        }
        return polyTag;
    }

    public VarPolynomial getSkelleton(final String name, final Map<String, BigIntegerInterval> ranges) {

        int i = 0;
        final Map<IndefinitePart, SimplePolynomial> resMap = new LinkedHashMap<IndefinitePart, SimplePolynomial>();

        for (final Map.Entry<IndefinitePart, SimplePolynomial> monomial : this.varMonomials.entrySet()) {
            final String freshname = name + i++;
            resMap.put(monomial.getKey(), SimplePolynomial.create(freshname));
            ranges.put(
                freshname,
                new BigIntegerInterval(monomial.getValue().min(ranges), monomial.getValue().max(ranges)));
        }
        //log.log(Level.FINEST, "A skelleton with " + i + " Monomials has been created.");
        return new VarPolynomial(resMap);

    }
}
