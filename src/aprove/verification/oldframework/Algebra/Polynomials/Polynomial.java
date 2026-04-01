package aprove.verification.oldframework.Algebra.Polynomials;

import java.io.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.input.Generated.polynomial.lexer.*;
import aprove.input.Generated.polynomial.node.*;
import aprove.input.Generated.polynomial.parser.*;
import aprove.input.Polynomials.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * Representation of multivariate polynomials with arbitrary degree.
 *
 * @deprecated Use VarPolynomial / SimplePolynomial.
 *
 * @author Andreas Capellmann
 * @version $Id$
 * docu-guess(thiemann):
 * A Polynomial is represented as a list of monomials that encodes the
 * sum of all monomials in the list
 */
@Deprecated
public class Polynomial extends LinkedList<Monomial> implements HTML_Able,
        PLAIN_Able,
        java.io.Serializable,
        XMLObligationExportable,
        CPFAdditional
{

  public static final Polynomial MINUS_ONE = Polynomial.createConstant(-1);
  public static final Polynomial ONE = Polynomial.createConstant(1);
  public static final Polynomial ZERO = Polynomial.createConstant(0);


/**
 * deepcopy
 */
  public static Polynomial create(final Polynomial p) {
      if (p == null) {
        return null;
    }
      final Polynomial newP = new Polynomial();
      for (final Object element : p) {
          final Monomial m = (Monomial) element;
          newP.add(m.deepcopy());
      }
      return newP;
  }

  public Polynomial deepcopy() {
      return Polynomial.create(this);
  }

  public List<Monomial> getList() {
      return this;
  }

  public static Polynomial create(final Monomial monomial) {
    final Polynomial p = new Polynomial();
    p.add(monomial);
    return p;
  }

  public static Polynomial createConstant(final int value) {
    final Polynomial p = new Polynomial();

    if (value != 0) {
        p.add(Monomial.create(value));
    }

    return p;
  }

  public static Polynomial createVariable(final String variable) {
    final Polynomial p = new Polynomial();
    p.add(Monomial.create(variable));

    return p;
  }

  /**
   * Parse the content of a string as a polynomial.
   *
   * @param string the string to parse
   * @return a new polynomial (<code>null</code> in case of parse error)
   */
  public static Polynomial parse(final String string) {
    try {
      final PushbackReader reader = new PushbackReader(new StringReader(string), 1024);
      final Parser parser = new Parser(new Lexer(reader));
      final Start tree = parser.parse();

      final Pass p = new Pass();
      tree.apply(p);

      return p.polynomial;
    } catch (final Exception e) {
      return null;
    }
  }

  public boolean allNegative() {
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      if (m.coeff > 0) {
        return false;
    }
    }

    return true;
  }

  public boolean allPositive() {
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      if (m.coeff < 0) {
        return false;
    }
    }

    return true;
  }

  /**
   * Check whether this polynomial contains a certain variable.
   *
   * @param variable the variable to search for
   * @return <code>true</code> if the polynomial contains the queried variable, <code>false</code>
   *   otherwise
   */
  public boolean containsVariable(final String variable) {
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      if (m.containsVariable(variable)) {
        return true;
    }
    }

    return false;
  }

  /**
   * Check whether this polynomial is equal to a certain number.
   *
   * @param value the number to check
   * @return <code>true</code> if this polynomial has the
   *   given value, <code>false</code> otherwise
   */
  public boolean equals(final int value) {
    if ((value == 0) && (this.isEmpty())) {
        return true;
    }

    return (this.size() == 1) && (this.getFirst().equals(value));
  }

  @Override
public boolean equals(final Object o) {
    if ((o == null) || (!(o instanceof Polynomial))) {
        return false;
    }

    return super.equals(o);
  }

  /**
   * Calculate the value of this polynomial with respect to the given values for the variables.
   *
   * @param values a mapping of variables names (instances of {@link java.lang.String}) to numbers
   *   (instances of {@link java.lang.Integer})
   * @return the new value of this polynomial according to the values of the variables
   */
  public long evaluate(final Map values) {
    long value = 0;
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      value += m.evaluate(values);
    }

    return value;
  }

    /**
     * docu-guess (fuhs):
     * Assuming a PolyConstraint (this = 0), the corresponding FiniteDomains
     * are created (according to Def. 4.3 of the paper where the search is
     * presented) and added to fdc.
     *
     * @param fdc the resulting FiniteDomains are added to fdc
     */
    /*
  public void getEqualityConstraints(FDConstraints fdc) {
    for (Iterator iter = this.iterator(); iter.hasNext();) {
      Monomial m = (Monomial) iter.next();

      if (m.isConstant())
        continue;

      Polynomial numerator = new Polynomial();
      numerator.addAll(this);
      numerator.remove(m);

      if (m.coeff > 0)
        numerator = numerator.times(-1);

      for (Entry<String, Integer> e : m.exponents.entrySet()) {

        int exponent = e.getValue().intValue();

        SortedMap<String, Integer> exponents = new TreeMap<String, Integer>(m.exponents);
        exponents.remove(e.getKey());

        FDBoundary lowerBound, upperBound;

        Polynomial denominator = null;
        if (exponents.isEmpty()) {
          if (Math.abs(m.coeff) != 1)
            denominator = Polynomial.createConstant(Math.abs(m.coeff));

        } else
          denominator = Polynomial.create(Monomial.create(Math.abs(m.coeff), exponents));

        lowerBound = FDBoundary.create(numerator, denominator, exponent);
        upperBound = FDBoundary.create(numerator, denominator, exponent);

        FiniteDomain fd = FiniteDomain.create((String) e.getKey(), lowerBound, upperBound);

        fdc.addConstraint(fd);
      }
    }
    */
    /*
        for (ListIterator iter = this.listIterator(); iter.hasNext();) {
          Monomial m = (Monomial) iter.next();

          if (m.isConstant())
            continue;

          for (Iterator iterator = m.exponents.entrySet().iterator(); iterator.hasNext();) {
            Entry e = (Entry) iterator.next();
            String variable = (String) e.getKey();

            Polynomial num = new Polynomial();
            num.addAll(this);
            num.remove(m);

            FDBoundary lowerBound = null;
            FDBoundary upperBound = null;

            for (int i = 0; i < 2; ++i) {

              Polynomial numerator;
              if (m.coeff > 0)
                numerator = num.times(-1);
              else
                numerator = num;

              if (i == 0)
                numerator = numerator.min();
              else
                numerator = numerator.max();

              int exponent = ((Integer) e.getValue()).intValue();

              SortedMap exponents = new TreeMap(m.exponents);
              exponents.remove(e.getKey());

              Polynomial denominator = null;
              if (exponents.isEmpty()) {
                if (Math.abs(m.coeff) != 1)
                  denominator = Polynomial.createConstant(Math.abs(m.coeff));

              } else {
                denominator = new Polynomial();
                denominator.add(Monomial.create(Math.abs(m.coeff), exponents));

                if (i == 0)
                  denominator = denominator.max();
                else
                  denominator = denominator.min();
              }

              if (i == 0) {
                lowerBound =
                  FDBoundary.create(numerator, denominator, exponent, FDBoundary.LOWER_BOUNDARY);
              } else {
                upperBound =
                  FDBoundary.create(numerator, denominator, exponent, FDBoundary.UPPER_BOUNDARY);
              }
            }

            FiniteDomain fd = FiniteDomain.create(variable, lowerBound, upperBound);
            fdc.addConstraint(fd);
          }
        }
        */
    /*
  }
    */

    /**
     * docu-guess (fuhs):
     * Assuming a PolyConstraint (this >= 0), the corresponding FiniteDomains
     * are created (according to Def. 4.3 of the paper where the search is
     * presented) and added to fdc.
     *
     * @param fdc the resulting FiniteDomains are added to fdc, and the upper
     *  bound for the resulting FiniteDomains is taken from fdc
     */
    /*
  public void getInequalityConstraints(FDConstraints fdc) {
    for (Iterator iter = this.iterator(); iter.hasNext();) {
      Monomial m = (Monomial) iter.next();

      if (m.isConstant())
        continue;

      Polynomial numerator = new Polynomial();
      numerator.addAll(this);
      numerator.remove(m);

      if (m.coeff > 0)
        numerator = numerator.times(-1);

      for (Entry<String, Integer> e : m.exponents.entrySet()) {

        int exponent = e.getValue().intValue();

        SortedMap<String, Integer> exponents = new TreeMap<String, Integer>(m.exponents);
        exponents.remove(e.getKey());

        FDBoundary lowerBound, upperBound;

        Polynomial denominator = null;
        if (exponents.isEmpty()) {
          if (Math.abs(m.coeff) != 1)
            denominator = Polynomial.createConstant(Math.abs(m.coeff));

        } else
          denominator = Polynomial.create(Monomial.create(Math.abs(m.coeff), exponents));

        String variable = (String) e.getKey();

        if (m.coeff > 0) {
          lowerBound =
            FDBoundary.create(numerator, denominator, exponent);
          upperBound =
            FDBoundary.create(
              Polynomial.createConstant(((Integer) fdc.ranges.get(variable)).intValue()));
        } else {
          lowerBound = FDBoundary.create(Polynomial.ZERO);
          upperBound =
            FDBoundary.create(numerator, denominator, exponent);
        }

        FiniteDomain fd = FiniteDomain.create(variable, lowerBound, upperBound);
        fdc.addConstraint(fd);
      }
    }
  }
    */

    /**
     * docu-guess (fuhs):
     * Counts how many times a product a_i * a_j or a_i^2 occurs in
     * this and increments the values of the mapping products
     * accordingly.
     *
     * @param products mapping [StringPair -> Integer] which keeps
     *  track of how many times a product of two variables (stored in
     *  the key of the mapping) has been observed. Note that the second
     *  variable of the StringPair is never smaller than the first one
     *  with respect to the natural order of String.
     */
  public void getProducts(final Map products) {
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      m.getProducts(products);
    }
  }

  /**
   * Get the set of variables that occur in this polynomial.
   *
   * @return the set of variables
   */
  public Set<String> getVariables() {
    final Set<String> variables = new LinkedHashSet<String>();
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      variables.addAll(m.getVariables());
    }

    return variables;
  }

  @Override
public int hashCode() {
    int code = 0;
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      code += m.hashCode();
    }

    return code;
  }

  private void insert(final Monomial monomial) {
    int c = -1;
    Monomial m = null;
    final ListIterator<Monomial> iter = this.listIterator();
    while (iter.hasNext()) {
      m = iter.next();
      c = m.compareExponents(monomial);

      if (c >= 0) {
        break;
    }
    }

    if (c < 0) {
      iter.add(monomial);

    } else if (c == 0) {
      iter.remove();

      final int coeff = m.coeff + monomial.coeff;

      if (coeff != 0) {
        iter.add(Monomial.create(coeff, m.exponents));
    }

    } else if (c > 0) {
      iter.previous();
      iter.add(monomial);
    }
  }

  public boolean isConstant() {
    if (this.isEmpty()) {
        return true;
    }

    return (this.size() == 1) && (this.getFirst().isConstant());
  }

  public boolean isVariable() {
    return (this.size() == 1) && (this.getFirst().isVariable());
  }

    /**
     * docu-guess (fuhs):
     * Computes the maximum value this can take given values.
     *
     * @param values mapping [String -> IntegerInterval] from variables to
     *  the interval in which possible values for the variables may lie
     * @return the maximum value this can take given values
     */
  public long max(final Map values) {
    long value = 0;
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      value += m.max(values);
    }

    return value;
  }

    /**
     * docu-guess (fuhs):
     * Computes the minimum value this can take given values.
     *
     * @param values mapping [String -> IntegerInterval] from variables to
     *  the interval in which possible values for the variables may lie
     * @return the minimum value this can take given values
     */
  public long min(final Map values) {
    long value = 0;
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      value += m.min(values);
    }

    return value;
  }

  /**
   * Subtract some polynomial from this polynomial.
   *
   * @param polynomial the subtrahend
   * @return the difference
   */
  public Polynomial minus(final Polynomial polynomial) {
    if (polynomial.isEmpty()) {
        return this;
    }

    final Polynomial sum = new Polynomial();

    final ListIterator<Monomial> leftIter = this.listIterator();
    final ListIterator<Monomial> rightIter = polynomial.listIterator();

    while ((leftIter.hasNext()) && (rightIter.hasNext())) {
      final Monomial left = leftIter.next();
      final Monomial right = rightIter.next();

      final int c = left.compareExponents(right);

      if (c < 0) {
        sum.add(left);
        rightIter.previous();
      } else if (c == 0) {
        final int coeff = left.coeff - right.coeff;
        if (coeff != 0) {
            sum.add(Monomial.create(coeff, left.exponents));
        }

      } else {
        sum.add(Monomial.create(-right.coeff, right.exponents));
        leftIter.previous();
      }
    }

    while (leftIter.hasNext()) {
        sum.add(leftIter.next());
    }

    while (rightIter.hasNext()) {
      final Monomial right = rightIter.next();
      sum.add(Monomial.create(-right.coeff, right.exponents));
    }

    return sum;
  }

  /**
   * Calculate the partial derivation of this polynomial with respect to the given variable.
   *
   * @param variable the variable to calculate the derivation for
   * @return the partial derivation
   */
  public Polynomial partiallyDerive(final String variable) {
    final Polynomial p = new Polynomial();
    final Polynomial q = new Polynomial();
    for (final Object element : this) {
      Monomial m = (Monomial) element;
      m = m.partiallyDerive(variable);

      if (m == null) {
        continue;
    }

      if (m.containsVariable(variable)) {
        p.add(m);
    } else {
        q.add(m);
    }
    }

    return p.plus(q);
  }

  /**
   * Add a given polynomial to this one.
   *
   * @param polynomial the addend
   * @return the sum of both polynomials
   */
  public Polynomial plus(final Polynomial polynomial) {
    if (this.isEmpty()) {
        return polynomial;
    }

    if (polynomial.isEmpty()) {
        return this;
    }

    final Polynomial sum = new Polynomial();

    final ListIterator<Monomial> leftIter = this.listIterator();
    final ListIterator<Monomial> rightIter = polynomial.listIterator();

    while ((leftIter.hasNext()) && (rightIter.hasNext())) {
      final Monomial left = leftIter.next();
      final Monomial right = rightIter.next();

      final int c = left.compareExponents(right);

      if (c < 0) {
        sum.add(left);
        rightIter.previous();
      } else if (c == 0) {
        final int coeff = left.coeff + right.coeff;
        if (coeff != 0) {
            sum.add(Monomial.create(coeff, left.exponents));
        }

      } else {
        sum.add(right);
        leftIter.previous();
      }
    }

    while (leftIter.hasNext()) {
        sum.add(leftIter.next());
    }

    while (rightIter.hasNext()) {
        sum.add(rightIter.next());
    }

    return sum;
  }

  /**
   * Raise the polynomial to the given power.
   *
   * @param exponent the exponent
   * @return this polynomial to the power of <code>exponent</code>
   */
  public Polynomial power(final int exponent) {
    if (exponent == 0) {
        return Polynomial.ONE;
    }

    if (exponent == 1) {
        return this;
    }

    final Polynomial p = this.times(this).power(exponent / 2);

    if (exponent % 2 == 0) {
        return p;
    }

    return p.times(this);
  }

    /**
     * docu-guess (fuhs):
     * Replaces x*y by z in this.
     * Modifies products accordingly.
     *
     * @param x one of the two factors of the product which is to be replaced
     * @param y the other factor of the product which is to be replaced
     * @param z replacement for x*y
     * @param products keeps track of how often each product of two variables
     *  occurs in the system (map StringPair -> Integer), is modified to suit
     *  the changes in this
     */
  public void replaceProducts(final String x, final String y, final String z, final Map products) {
    if ((!this.containsVariable(x)) || (!(this.containsVariable(y)))) {
        return;
    }

    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      m.replaceProducts(x, y, z, products);
    }
  }
    /**
     * simplifies a Polynomial that encodes an activation Condition
     */
    public Polynomial simplifyActiveCondition(final Abortion aborter) throws AbortionException {

        final boolean doChecks = this.size() > 50; // check timer if we have a big polynomial

        // 1) set all exponents to one, ignore coefficients,
        //     remove superfluous conditions
        final HashSet<Set<String>> allCoeffs = new HashSet<Set<String>>();
        for (final Monomial m : this) {
            if (doChecks) {
                aborter.checkAbortion();
            }
            final Set<String> coeffs = m.exponents.keySet();
            // check if stronger condition is already inserted
            if (Collection_Util.isSuperSetOf(coeffs,allCoeffs)) {
                continue;
            }
            if (doChecks) {
                aborter.checkAbortion();
            }
            // okay, so we have to insert this monomial
            // discard all weaker conditions first
            final Set<Set<String>> moreExponents = Collection_Util.getSuperSetsOf(coeffs,allCoeffs);
            allCoeffs.removeAll(moreExponents);
            // and insert into the set of coeffs
            allCoeffs.add(coeffs);
        }
        // 2) build polynomial
        final Polynomial p = new Polynomial();
        for (final Set<String> coeffs : allCoeffs) {
            p.insert(Monomial.createCoeffExpOne(coeffs));
        }
        return p;
    }

    /**
     * docu-guess (fuhs):
     * Replaces x^2 by z in this.
     * products is modified accordingly in the process.
     *
     * @param x x^2 is to be replaced in this
     * @param z replacement for x^2
     * @param products keeps track of how often each product of two variables
     *  occurs in the system (map StringPair -> Integer), is modified to suit
     *  the changes in this
     */
  public void replaceSquares(final String x, final String z, final Map products) {
    if (!this.containsVariable(x)) {
        return;
    }

    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      m.replaceSquares(x, z, products);
    }
  }

  public Polynomial setVariableToZero(final String variable) {
    final Polynomial p = new Polynomial();
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      if (!(m.containsVariable(variable))) {
        p.add(m);
    }
    }

    return p;
  }

  /**
   * Replace all occurences of a variable with a given substitute.
   *
   * @param variable the variable to replace
   * @param substitute the substitue
   * @return a new polynomial where <code>variable</code> is replaced by <code>substitute</code>
   */
  public Polynomial substituteVariable(final String variable, final Polynomial substitute) {
    if (substitute.isEmpty()) {
        return this.setVariableToZero(variable);
    }

    final Polynomial p = new Polynomial();
    Polynomial q = new Polynomial();
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      final Polynomial sub = m.substitute(variable, substitute);

      if (sub == null) {
        p.insert(m);
    } else {
        q = q.plus(sub);
    }
    }

    return p.plus(q);
  }

  private Polynomial times(final int value) {
    final Polynomial p = new Polynomial();
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      p.add(Monomial.create(m.coeff * value, m.exponents));
    }

    return p;
  }

  protected Polynomial times(final Monomial monomial) {
    final Polynomial p = new Polynomial();
    for (final Object element : this) {
      final Monomial m = (Monomial) element;
      p.insert(m.times(monomial));
    }

    return p;
  }

  /**
   * Multiply this polynomial with another one.
   *
   * @param polynomial the factor
   * @return the product of both polynomials
   */
  public Polynomial times(final Polynomial polynomial) {
    if ((this.equals(0)) || (polynomial.equals(1))) {
        return this;
    }

    if ((this.equals(1)) || (polynomial.equals(0))) {
        return polynomial;
    }

    if (polynomial.isConstant()) {
        return this.times(this.getFirst().coeff);
    }

    Polynomial p = Polynomial.ZERO;
    for (final Object element : polynomial) {
      final Monomial m = (Monomial) element;
      p = p.plus(this.times(m));
    }

    return p;
  }

  public Polynomial getCoefficientForVariable(final String x, final Set<String> xs) {
      Polynomial c = Polynomial.ZERO;
      for (final Monomial m : this) {
          c = c.plus(m.getCoefficientForVariable(x, xs));
      }
      return c;
  }

  /**
   * takes the set of variables and then computes
   * the set of corresponding coefficients for each of
   * these variables
   * @param xs the set of variables
   * @return a mapping from variables to coefficients
   */
  public Set<Polynomial> getAllCoefficients(final Set<String> xs) {
      final Map<Polynomial, Polynomial> map = new LinkedHashMap<Polynomial, Polynomial>();

      // iterate over all monomials
      for (final Monomial m : this) {
          final Pair<Polynomial, Polynomial> pair = m.splitCoefficient(xs);
          final Polynomial vars = pair.getKey();

          // lookup old coefficient for vars
          Polynomial oldCoeff = map.get(vars);
          if (oldCoeff == null) {
              oldCoeff = Polynomial.ZERO;
          }

          // and store new one
          oldCoeff = oldCoeff.plus(pair.getValue());
          map.put(vars, oldCoeff);
      }

      // finally collect all Coefficients from Map
      return new LinkedHashSet<Polynomial>(map.values());
  }

  /**
   * Calculate the HTML representation of this polynomial.
   *
   * @return the HTML representation of this polynomial
   */
  @Override
public String toHTML() {
    if (this.isEmpty()) {
        return String.valueOf(0);
    }

    final StringBuffer b = new StringBuffer();
    for (final Object element : this) {
      final Monomial m = (Monomial) element;

      if (b.length() > 0) {
        b.append(" + ");
    }

      b.append(m.toHTML());
    }

    return b.toString();
  }

    @Override
    public String toPLAIN() {

    if (this.isEmpty()) {
        return String.valueOf(0);
    }

    final StringBuffer b = new StringBuffer();
    for (final Object element : this) {
        final Monomial m = (Monomial) element;

        if (b.length() > 0) {
            b.append(" + ");
        }

        b.append(m.toPLAIN());
    }

    return b.toString();

    }

  /**
   * Calculate the LaTeX representation of this polynomial.
   *
   * @return the LaTeX representation of this polynomial
   */
  public String toLaTeX() {
    if (this.isEmpty()) {
        return String.valueOf(0);
    }

    final StringBuffer b = new StringBuffer();
    for (final Object element : this) {
      final Monomial m = (Monomial) element;

      if (b.length() > 0) {
        b.append(" + ");
    }

      b.append(m.toLaTeX());
    }

    return b.toString();
  }

  /**
   * Calculate the string representation of this polynomial.
   *
   * @return the string representation of this polynomial
   */
  @Override
public String toString() {
    if (this.isEmpty()) {
        return String.valueOf(0);
    }

    final StringBuffer b = new StringBuffer();
    for (final Object element : this) {
      final Monomial m = (Monomial) element;

      if (b.length() > 0) {
        b.append(" + ");
    }

      b.append(m.toString());
    }

    return b.toString();
  }

    /**
     * Calculate the string representation of this polynomial.
     *
     * @return the string representation of this polynomial
     */
    public String toString(final String newVar, final String prefix) {
        if (this.isEmpty()) {
            return String.valueOf(0);
        }

        final StringBuffer b = new StringBuffer();
        for (final Object element : this) {
            final Monomial m = (Monomial) element;

            if (b.length() > 0) {
                b.append(" + ");
            }

            b.append(m.toString(newVar, prefix));
        }

        return b.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element poly = XMLTag.POLYNOMIAL.createElement(doc);
        if (this.isEmpty()) {
            final Element monomial = XMLTag.MONOMIAL.createElement(doc);
            monomial.appendChild(XMLTag.createInteger(doc, 0));
            poly.appendChild(monomial);
            return poly;
        }
        for (final Monomial m : this) {
            poly.appendChild(m.toDOM(doc, xmlMetaData));
        }
        return poly;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element arithFunction = CPFTag.ARITH_FUNCTION.createElement(doc);
        switch (this.size()) {
        case 0:
            final Element natural = CPFTag.NATURAL.createElement(doc);
            natural.appendChild(doc.createTextNode("" + 0));
            arithFunction.appendChild(natural);
            break;
        case 1:
            for (final Monomial m : this) {
                return m.toCPF(doc, xmlMetaData);
            }
            break;
        default:
            final Element sum = CPFTag.SUM.createElement(doc);
            for (final Monomial m : this) {
                sum.appendChild(m.toCPF(doc, xmlMetaData));
            }
            arithFunction.appendChild(sum);
        }
        return arithFunction;
    }

}
