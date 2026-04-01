package aprove.verification.oldframework.Algebra.Polynomials;

import java.util.*;
import java.util.Map.Entry;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 *
 * @deprecated
 *
 * docu-guess (thiemann):
 * A Monomial c*x1^p1*...*xn^pn is represented by the coefficiet c
 * and a map from variables(Strings) xi to exponents pi
 */
@Deprecated
public class Monomial implements HTML_Able, PLAIN_Able, LaTeX_Able, XMLObligationExportable, CPFAdditional {

    public final int coeff;
    public final SortedMap<String, Integer> exponents;

    private Monomial(final int coeff, final SortedMap<String, Integer> exponents) {
        this.coeff = coeff;
        this.exponents = exponents;
    }

    public static Monomial create(final int coeff) {
        return new Monomial(coeff, new TreeMap<String, Integer>());
    }

    public static Monomial create(final int coeff, final SortedMap<String, Integer> exponents) {
        return new Monomial(coeff, exponents);
    }

    public static Monomial create(final String variable) {
        final SortedMap<String, Integer> exponents = new TreeMap<String, Integer>();
        exponents.put(variable, Integer.valueOf(1));

        return new Monomial(1, exponents);
    }

    public int getCoeff() {
        return this.coeff;
    }

    public SortedMap<String, Integer> getExponents() {
        return this.exponents;
    }

    public int compareExponents(final Monomial m) {
        final Iterator leftIter = this.exponents.entrySet().iterator();
        final Iterator rightIter = m.exponents.entrySet().iterator();

        while ((leftIter.hasNext()) && (rightIter.hasNext())) {
            final Entry left = (Entry) leftIter.next();
            final Entry right = (Entry) rightIter.next();

            int c = ((String) left.getKey()).compareTo((String) right.getKey());

            if (c != 0) {
                return c;
            }

            c = ((Integer) left.getValue()).compareTo((Integer) right.getValue());

            if (c != 0) {
                return c;
            }
        }

        if (leftIter.hasNext()) {
            return 1;
        } else if (rightIter.hasNext()) {
            return -1;
        } else {
            return 0;
        }
    }

    public boolean containsVariable(final String variable) {
        return this.exponents.containsKey(variable);
    }

    public Monomial deepcopy() {
        final SortedMap<String, Integer> exponents = new TreeMap<String, Integer>(this.exponents);
        return new Monomial(this.coeff, exponents);
    }

    public boolean equals(final int value) {
        return (this.exponents.isEmpty()) && (this.coeff == value);
    }

    @Override
    public boolean equals(final Object o) {
        if ((o == null) || (!(o instanceof Monomial))) {
            return false;
        }

        final Monomial m = (Monomial) o;

        return (this.coeff == m.coeff) && (this.exponents.equals(m.exponents));
    }

    public long evaluate(final Map values) {
        long value = this.coeff;
        for (final Object element : this.exponents.entrySet()) {
            final Entry e = (Entry) element;
            value *= Math.pow(((Integer) values.get(e.getKey())).intValue(), ((Integer) e.getValue()).intValue());
        }

        return value;
    }

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
        for (final Object element : this.exponents.entrySet()) {
            final Entry headEntry = (Entry) element;
            final String variable = (String) headEntry.getKey();

            final int headExp = ((Integer) headEntry.getValue()).intValue();

            // check for squares
            if (headExp > 1) {
                this.updateProducts(new StringPair(variable, variable), headExp / 2, products);
            }

            // count binary product of different variables
            final Iterator tail = this.exponents.tailMap(variable).entrySet().iterator();
            if (tail.hasNext()) {
                tail.next();
            }

            while (tail.hasNext()) {
                final Entry tailEntry = (Entry) tail.next();
                final int tailExp = ((Integer) tailEntry.getValue()).intValue();

                final int min = Math.min(headExp, tailExp);
                if (min > 0) {
                    this.updateProducts(new StringPair(variable, (String) tailEntry.getKey()), min, products);
                }
            }
        }
    }

    public Set<String> getVariables() {
        return this.exponents.keySet();
    }

    public Set<String> getVariables(final String prefix) {
        final Set<String> res = new HashSet<String>(this.getVariables());
        final Iterator<String> i = res.iterator();
        while (i.hasNext()) {
            final String name = i.next();
            if (!name.startsWith(prefix)) {
                i.remove();
            }
        }
        return res;
    }

    @Override
    public int hashCode() {
        int code = this.coeff;
        for (final Object element : this.exponents.entrySet()) {
            final Entry e = (Entry) element;
            code *= Math.pow(e.getKey().hashCode(), ((Integer) e.getValue()).intValue());
        }

        return code;
    }

    public boolean isConstant() {
        return this.exponents.isEmpty();
    }

    public boolean isVariable() {
        if ((this.coeff == 1)
            && (this.exponents.size() == 1)
            && (this.exponents.values().iterator().next().intValue() == 1))
        {
            return true;
        }

        return false;
    }

    /**
     * docu-guess (fuhs):
     * Return the maximal value of the variable part of this given
     * values.
     *
     * @param values mapping [String -> IntegerInterval] which assigns
     *  minimal and maximal values to variables.
     * @return the maximum value the variable part of this can take
     *  with values as variable-to-interval assignment
     */
    private long maxWithoutCoeff(final Map values) {
        long value = 1;
        for (final Object element : this.exponents.entrySet()) {
            final Entry e = (Entry) element;
            value *= Math.pow(((IntegerInterval) values.get(e.getKey())).max, ((Integer) e.getValue()).intValue());
        }

        return value;
    }

    /**
     * docu-guess (fuhs):
     * Return the minimal value of the variable part of this given
     * values.
     *
     * @param values mapping [String -> IntegerInterval] which assigns
     *  minimal and maximal values to variables.
     * @return the minimum value the variable part of this can take
     *  with values as variable-to-interval assignment
     */
    private long minWithoutCoeff(final Map values) {
        long value = 1;
        for (final Object element : this.exponents.entrySet()) {
            final Entry e = (Entry) element;
            value *= Math.pow(((IntegerInterval) values.get(e.getKey())).min, ((Integer) e.getValue()).intValue());
        }

        return value;
    }

    /**
     * docu-guess (fuhs):
     * Compute the maximal value of this, given values.
     *
     * @param values mapping [String -> IntegerInterval] which assigns
     *  minimal and maximal values to variables.
     * @return the maximum value this can take given values as
     *  variable-to-interval assignment.
     */
    public long max(final Map values) {
        if (this.coeff > 0) {
            return this.coeff * this.maxWithoutCoeff(values);
        } else {
            return this.coeff * this.minWithoutCoeff(values);
        }
    }

    /**
     * docu-guess (fuhs):
     * Compute the minimal value of this, given values.
     *
     * @param values mapping [String -> IntegerInterval] which assigns
     *  minimal and maximal values to variables.
     * @return the minimum value this can take given values as
     *  variable-to-interval assignment.
     */
    public long min(final Map values) {
        if (this.coeff > 0) {
            return this.coeff * this.minWithoutCoeff(values);
        } else {
            return this.coeff * this.maxWithoutCoeff(values);
        }
    }

    public Monomial partiallyDerive(final String variable) {
        final Integer exponent = this.exponents.get(variable);

        if (exponent == null) {
            return null;
        }

        final int exp = exponent.intValue();

        final SortedMap<String, Integer> exponents = new TreeMap<String, Integer>(this.exponents);
        if (exp == 1) {
            exponents.remove(variable);
        } else {
            exponents.put(variable, Integer.valueOf(exp - 1));
        }

        return new Monomial(this.coeff * exp, exponents);
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
     *  the changes in this; (x, y) is assumed not to occur in products
     *  any more when replaceProducts(...) is called
     */
    public void replaceProducts(final String x, final String y, final String z, final Map products) {
        Integer exponent = this.exponents.get(x);
        if (exponent == null) {
            return;
        }
        final int xExponent = exponent.intValue();

        exponent = this.exponents.get(y);
        if (exponent == null) {
            return;
        }
        final int yExponent = exponent.intValue();

        final int minExponent = Math.min(xExponent, yExponent);
        if (minExponent < 1) {
            return;
        }
        if (minExponent > 1) {
            this.updateProducts(new StringPair(z, z), minExponent / 2, products);
        }

        if (xExponent == yExponent) {
            for (final Object element : this.exponents.entrySet()) {
                final Entry e = (Entry) element;
                final String var = (String) e.getKey();

                if ((var.equals(x)) || (var.equals(y))) {
                    continue;
                }

                final int exp = ((Integer) e.getValue()).intValue();

                this.updateProducts(new StringPair(x, var), -Math.min(xExponent, exp), products);
                this.updateProducts(new StringPair(y, var), -Math.min(yExponent, exp), products);
                this.updateProducts(new StringPair(z, var), Math.min(minExponent, exp), products);
            }

            this.updateProducts(new StringPair(x, x), -(xExponent / 2), products);
            this.updateProducts(new StringPair(y, y), -(yExponent / 2), products);

            this.exponents.remove(x);
            this.exponents.remove(y);

        } else if (xExponent < yExponent) {
            for (final Object element : this.exponents.entrySet()) {
                final Entry e = (Entry) element;
                final String var = (String) e.getKey();

                if ((var.equals(x)) || (var.equals(y))) {
                    continue;
                }

                final int exp = this.exponents.get(var).intValue();

                this.updateProducts(new StringPair(x, var), -Math.min(xExponent, exp), products);
                this.updateProducts(
                    new StringPair(y, var),
                    Math.min(yExponent - xExponent, exp) - Math.min(yExponent, exp),
                    products);
                this.updateProducts(new StringPair(z, var), Math.min(minExponent, exp), products);
            }

            this.updateProducts(new StringPair(x, x), -(xExponent / 2), products);
            this.updateProducts(new StringPair(y, y), ((yExponent - xExponent) / 2) - (yExponent / 2), products);

            this.exponents.remove(x);
            this.exponents.put(y, Integer.valueOf(yExponent - xExponent));

        } else {
            for (final Object element : this.exponents.entrySet()) {
                final Entry e = (Entry) element;
                final String var = (String) e.getKey();

                if ((var.equals(x)) || (var.equals(y))) {
                    continue;
                }

                final int exp = this.exponents.get(var).intValue();

                this.updateProducts(
                    new StringPair(x, var),
                    Math.min(xExponent - yExponent, exp) - Math.min(xExponent, exp),
                    products);
                this.updateProducts(new StringPair(y, var), -Math.min(yExponent, exp), products);
                this.updateProducts(new StringPair(z, var), Math.min(minExponent, exp), products);
            }

            this.updateProducts(new StringPair(x, x), ((xExponent - yExponent) / 2) - (xExponent / 2), products);
            this.updateProducts(new StringPair(y, y), -(yExponent / 2), products);

            this.exponents.put(x, Integer.valueOf(xExponent - yExponent));
            this.exponents.remove(y);
        }

        this.exponents.put(z, Integer.valueOf(minExponent));
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
     *  the changes in this; (x, x) is assumed not to occur in products any
     *  more when replaceSquares(...) is called
     */
    public void replaceSquares(final String x, final String z, final Map products) {
        final Integer exponent = this.exponents.get(x);
        if (exponent == null) {
            return;
        }
        final int xExponent = exponent.intValue();

        if (xExponent < 2) {
            return;
        }

        final int xExponentHalf = xExponent / 2;

        this.updateProducts(new StringPair(z, z), xExponentHalf / 2, products);

        if (xExponent % 2 == 0) {
            for (final Object element : this.exponents.entrySet()) {
                final Entry e = (Entry) element;
                final String var = (String) e.getKey();
                final int exp = ((Integer) e.getValue()).intValue();

                this.updateProducts(new StringPair(x, var), -Math.min(xExponent, exp), products);

                if (!var.equals(x)) {
                    this.updateProducts(new StringPair(z, var), Math.min(xExponentHalf, exp), products);
                }
            }

            this.exponents.remove(x);

        } else {
            for (final Object element : this.exponents.entrySet()) {
                final Entry e = (Entry) element;
                final String var = (String) e.getKey();
                final int exp = ((Integer) e.getValue()).intValue();

                this.updateProducts(new StringPair(x, var), 1 - Math.min(xExponent, exp), products);

                if (!var.equals(x)) {
                    this.updateProducts(new StringPair(z, var), Math.min(xExponentHalf, exp), products);
                }
            }

            this.updateProducts(new StringPair(x, z), 1, products);
            this.exponents.put(x, Integer.valueOf(1));
        }

        this.exponents.put(z, Integer.valueOf(xExponentHalf));
    }

    public Polynomial substitute(final String variable, Polynomial substitute) {
        final Integer exponent = this.exponents.get(variable);

        if (exponent == null) {
            return null;
        }

        substitute = substitute.power(exponent.intValue());

        final SortedMap<String, Integer> exponents = new TreeMap<String, Integer>(this.exponents);
        exponents.remove(variable);

        return substitute.times(new Monomial(this.coeff, exponents));
    }

    protected Monomial times(final Monomial monomial) {
        final SortedMap<String, Integer> exponents = new TreeMap<String, Integer>(this.exponents);
        for (final Entry<String, Integer> e : monomial.exponents.entrySet()) {
            final Integer exponent = exponents.get(e.getKey());
            if (exponent == null) {
                exponents.put(e.getKey(), e.getValue());
            } else {
                exponents.put(e.getKey(), Integer.valueOf(e.getValue().intValue() + exponent.intValue()));
            }
        }

        return new Monomial(this.coeff * monomial.coeff, exponents);
    }

    /**
     * if xs are the variables in polynomials, this method
     * looks whether the monomial does only contain the
     * variable x in power 1 and then returns the corresponding
     * coefficient (monomial / x)
     * @param x
     * @param xs
     * @return
     */
    Polynomial getCoefficientForVariable(final String x, final Set<String> xs) {
        final Integer power = this.exponents.get(x);
        if (power == null) {
            return Polynomial.ZERO;
        }
        final int pow = power.intValue();
        if (pow != 1) {
            return Polynomial.ZERO;
        }
        final Monomial copy = this.deepcopy();
        copy.exponents.remove(x);
        for (final String varCoff : copy.exponents.keySet()) {
            if (xs.contains(varCoff)) {
                return Polynomial.ZERO;
            }
        }
        return Polynomial.create(copy);
    }

    /**
     * takes the variables xs and splits the monomial
     * into the pair of (variable part, coefficient part)
     * @param xs
     * @return
     */
    Pair<Polynomial, Polynomial> splitCoefficient(final Set<String> xs) {
        SortedMap<String, Integer> vars, coeffs;
        vars = new TreeMap<String, Integer>();
        coeffs = new TreeMap<String, Integer>();

        // iterate over all var / coeffs and put them
        // in the corresponding map

        for (final Entry<String, Integer> e : this.exponents.entrySet()) {
            final String varCoeff = e.getKey();
            if (xs.contains(varCoeff)) {
                // we have a variable
                vars.put(varCoeff, e.getValue());
            } else {
                // we have a coefficient
                coeffs.put(varCoeff, e.getValue());
            }
        }

        // finally create the corresponding monomials and polynomials
        final Polynomial vp = Polynomial.create(new Monomial(1, vars));
        final Polynomial cp = Polynomial.create(new Monomial(this.coeff, coeffs));
        return new Pair<Polynomial, Polynomial>(vp, cp);
    }

    @Override
    public String toHTML() {
        final StringBuffer b = new StringBuffer();
        b.append(this.coeff);

        final String mult = "&middot;";

        if (!(this.exponents.isEmpty())) {
            for (final Object element : this.exponents.entrySet()) {
                final Entry e = (Entry) element;
                b.append(mult);

                // variable output
                final String[] parts = ((String) e.getKey()).split("_");
                for (int i = 0; i < parts.length; i++) {
                    if (i != 0) {
                        b.append("<sub>");
                    }

                    b.append(parts[i]);
                }
                for (int i = 0; i < parts.length - 1; i++) {
                    b.append("</sub>");
                }

                final int exponent = ((Integer) e.getValue()).intValue();
                if (exponent != 1) {
                    b.append("<sup>");
                    b.append(exponent);
                    b.append("</sup>");
                }
            }
        }

        if ((this.coeff == 1) && (b.length() > 1)) {
            b.delete(0, mult.length() + 1);
        }

        return b.toString();
    }

    @Override
    public String toPLAIN() {

        final StringBuffer b = new StringBuffer();
        b.append(this.coeff);

        final String mult = "*";

        if (!(this.exponents.isEmpty())) {
            final Iterator iter = this.exponents.entrySet().iterator();
            while (iter.hasNext()) {
                final Entry e = (Entry) iter.next();
                b.append(mult);

                // variable output
                final String[] parts = ((String) e.getKey()).split("_");
                for (int i = 0; i < parts.length; i++) {
                    if (i > 0) {
                        b.append("_");
                    }
                    b.append(parts[i]);
                }

                final int exponent = ((Integer) e.getValue()).intValue();
                if (exponent != 1) {
                    b.append(exponent);
                }
            }
        }

        if ((this.coeff == 1) && (b.length() > 1)) {
            b.delete(0, mult.length() + 1);
        }

        return b.toString();

    }

    @Override
    public String toLaTeX() {
        final StringBuffer b = new StringBuffer();
        b.append(this.coeff);

        final String mult = "";

        if (!(this.exponents.isEmpty())) {
            for (final Object element : this.exponents.entrySet()) {
                final Entry e = (Entry) element;
                b.append(mult);

                // variable output
                final String[] parts = ((String) e.getKey()).split("_");
                for (int i = 0; i < parts.length; i++) {
                    if (i != 0) {
                        b.append("_{");
                    }

                    b.append(parts[i]);
                }
                for (int i = 0; i < parts.length - 1; i++) {
                    b.append("}");
                }

                final int exponent = ((Integer) e.getValue()).intValue();
                if (exponent != 1) {
                    b.append("^");
                    b.append(exponent);
                }
            }
        }

        if ((this.coeff == 1) && (b.length() > 1)) {
            b.delete(0, mult.length() + 1);
        }

        return b.toString();
    }

    @Override
    public String toString() {
        final StringBuffer b = new StringBuffer();
        b.append(this.coeff);

        final String mult = "*";

        if (!(this.exponents.isEmpty())) {
            for (final Object element : this.exponents.entrySet()) {
                final Entry e = (Entry) element;
                b.append(mult);
                b.append(e.getKey());

                final int exponent = ((Integer) e.getValue()).intValue();
                if (exponent != 1) {
                    b.append("^");
                    b.append(exponent);
                }
            }
        }

        if ((this.coeff == 1) && (b.length() > 1)) {
            b.delete(0, mult.length() + 1);
        }

        return b.toString();
    }

    public String toString(final String newVar, final String prefix) {
        final StringBuffer b = new StringBuffer();
        b.append(this.coeff);

        final String mult = "*";

        if (!(this.exponents.isEmpty())) {
            for (final Object element : this.exponents.entrySet()) {
                final Entry e = (Entry) element;
                b.append(mult);
                String strr = (String) e.getKey();
                if (!strr.startsWith(prefix)) {
                    strr = new String(newVar);
                }
                b.append(strr);

                final int exponent = ((Integer) e.getValue()).intValue();
                if (exponent != 1) {
                    b.append("^");
                    b.append(exponent);
                }
            }
        }

        if ((this.coeff == 1) && (b.length() > 1)) {
            b.delete(0, mult.length() + 1);
        }

        return b.toString();
    }

    /**
     * docu-guess (fuhs):
     * Increments the count of pair in products by value.
     *
     * @param pair a pair of variables
     * @param value the value by which the count of pair is to be incremented
     *  in products
     * @param products mapping [StringPair -> Integer], used for keeping track
     *  of how many times a product of two variables has been seen
     */
    private void updateProducts(final StringPair pair, final int value, final Map products) {
        final Integer count = (Integer) products.get(pair);

        if (count == null) {
            products.put(pair, Integer.valueOf(value));
        } else {
            products.put(pair, Integer.valueOf(value + count.intValue()));
        }
    }

    /**
     * creates a simplified monomial, where all exponents of the
     * coefficients/variables are one,
     * and also the coefficient/constant factor is one
     */
    public static Monomial createCoeffExpOne(final Set<String> coeffs) {
        final SortedMap<String, Integer> exp = new TreeMap<String, Integer>();
        for (final String var : coeffs) {
            exp.put(var, Integer.valueOf(1));
        }
        return (new Monomial(1, exp));
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element mon = XMLTag.MONOMIAL.createElement(doc);
        mon.appendChild(XMLTag.createInteger(doc, this.coeff));
        for (final Entry<String, Integer> entry : this.exponents.entrySet()) {
            final Element productTag = XMLTag.INDEFINIT.createElement(doc);
            final Element varNode = XMLTag.VARIABLE.createElement(doc);
            XMLAttribute.VARNAME.setAttribute(varNode, entry.getKey());
            productTag.appendChild(varNode);
            productTag.appendChild(XMLTag.createInteger(doc, entry.getValue()));
            mon.appendChild(productTag);
        }
        return mon;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element coeff =
            CPFTag.ARITH_FUNCTION.create(doc, CPFTag.NATURAL.create(doc, doc.createTextNode(this.coeff + "")));
        if (this.exponents.isEmpty()) {
            return coeff;
        } else {
            final Element prod = CPFTag.PRODUCT.create(doc, coeff);
            for (final Map.Entry<String, Integer> e : this.exponents.entrySet()) {
                final String varName = (Integer.parseInt(e.getKey().substring(2)) + 1) + "";
                for (int i = 0; i < e.getValue(); i++) {
                    prod.appendChild(CPFTag.ARITH_FUNCTION.create(
                        doc,
                        CPFTag.VARIABLE.create(doc, doc.createTextNode(varName))));
                }
            }
            return CPFTag.ARITH_FUNCTION.create(doc, prod);
        }
    }

}
