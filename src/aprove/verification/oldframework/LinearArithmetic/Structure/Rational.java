package aprove.verification.oldframework.LinearArithmetic.Structure;

import aprove.prooftree.Export.Utility.*;

/**
 * A class for rational numbers.
 * To avoid overflows numerator and denominator get reduced every time possible.
 *
 * At the end of each operation the rational is in reduced form. This means the
 * greates common divisor (gcd) of numerator and denominator is always 1. Thus
 * after each modification there will be a reduction step. The denominator is
 * always a positive integer. Hence negative values are represented by a
 * negative numerator.
 *
 * There is another component: m
 * This symbolizes very large penaltiy costs.
 * m is itself an instance of Rational.
 * So be aware not to create infinite callings in the constructors.
 * By default m is therefore set to null.
 *
 * Note that there are operations which cannot be done with the m component:
 * creating the reciprocal
 * thus dividing by and
 * multiplication of two m values.
 *
 * @author dickmeis
 */

public class Rational implements Comparable, Exportable {

    public final static Rational zero = new Rational();

    private int numerator; // the numerator // (german: Zaehler)
    private int denominator; // the denominator // (german: Nenner)

    private final Rational m;

    /**
     * Constructs a new rational numerator / denominator
     * and reduce it if possible
     *
     * @param numerator
     * @param denominator
     */
    public Rational(final int numerator, final int denominator) {
        this(numerator, denominator, null);
    }

    /**
     * Constructs a new rational numerator / denominator + m-component
     * and reduce it if possible.
     *
     * @param numerator
     * @param denominator
     * @param m
     */
    public Rational(final int numerator, final int denominator, final Rational m) {
        final int g = Rational.gcd(numerator, denominator);
        this.numerator = numerator / g;
        this.denominator = denominator / g;

        // only needed for negative numbers
        if (this.denominator < 0) {
            this.denominator = -this.denominator;
            this.numerator = -this.numerator;
        }

        this.m = m;
    }

    /**
     * Constructs a new rational from a ration and another as m-component
     * and reduce it if possible.
     *
     * @param r the normal component
     * @param m the m-component
     */
    public Rational(final Rational r, final Rational m) {
        this.numerator = r.numerator;
        this.denominator = r.denominator;

        this.m = m;
    }

    /**
     * Creates a rational consisting of a negative m component.
     *
     * @return rational consisting of a negative m component.
     */
    public static Rational createMinusM() {
        return new Rational(Rational.zero, new Rational(-1));
    }

    /**
     * Constructs a rational with the value 0
     */
    public Rational() {
        this.numerator = 0;
        this.denominator = 1;

        this.m = null;
    }

    /**
     * Constructs a rational with the value n
     * @param n
     */
    public Rational(final int n) {
        this.numerator = n;
        this.denominator = 1;

        this.m = null;
    }

    /**
     * Copies the object.
     *
     * @return a copy of the object
     */
    public Rational deepcopy() {
        if (this.m == null) {
            return new Rational(this.numerator, this.denominator);
        } else {
            return new Rational(this.numerator, this.denominator, this.m.deepcopy());
        }
    }

    /**
     * Returns the numerator (german: Zaehler).
     *
     * @return numerator
     */
    public int getNumerator() {
        return this.numerator;
    }

    /**
     * Returns the denominator (german: Nenner).
     *
     * @return denominator
     */
    public int getDenominator() {
        return this.denominator;
    }

    /**
     * Returns whether there is an active M
     *
     * @return m
     */
    public boolean isM() {
        return this.m != null && !this.m.equals(Rational.zero);
    }

    /**
     * Returns a double precision representation.
     *
     * @return a double precision representation
     */
    public double toDouble() {
        if (this.m == null || this.m.equals(Rational.zero)) {
            return (double) this.numerator / this.denominator;
        } else {
            return Double.MAX_VALUE;
        }
    }

    /**
     * Returns a string representation.
     *
     * @return a string representation
     */
    @Override
    public String toString() {
        if (this.m == null || this.m.compareTo(Rational.zero) == 0) {
            if (this.denominator == 1) {
                return this.numerator + "";
            } else {
                return this.numerator + "/" + this.denominator;
            }
        } else {
            if (this.numerator == 0) {
                return "M*" + this.m;
            } else if (this.denominator == 1) {
                return "M*" + this.m + " + " + this.numerator;
            } else {
                return "M*" + this.m + " + " + this.numerator + "/" + this.denominator;
            }

        }
    }

    /**
     * Compares if this is equal to the given rational.
     * Returns true if this = r, and otherwise false.
     *
     * @param r the rational to compare with
     * @return true if this = r, otherwise false
     */
    public boolean equals(final Rational r) {
        return this.compareTo(r) == 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final Rational other = (Rational) obj;
        return this.equals(other);
    }

    /**
     * Calculates the greates common divisor of |m| and |n|.
     * Please note that the absolute value is taken.
     *
     * @param m
     * @param n
     *
     * @return the greates common divisor
     */
    // return gcd(|m|, |n|)
    public static int gcd(int m, int n) {

        if (m < 0) {
            m = -m;
        }
        if (n < 0) {
            n = -n;
        }

        int r;
        while (true) {
            if (n == 0) {
                return m;
            } else {
                r = m % n;
                m = n;
                n = r;
            }
        }
    }

    /**
     * Calculates the greates common divisor of |a| and |b|.
     * Please note that the absolute value is taken.
     *
     * @param a
     * @param b
     *
     * @return the greates common divisor
     */
    public static Rational gcd(final Rational a, final Rational b) {

        if (a.denominator != 1 || b.denominator != 1) {
            return new Rational(1);
        }

        final int g = Rational.gcd(a.numerator, b.numerator);

        return new Rational(g);
    }

    /**
     * Calculates the least common multiple of |m| and |n|.
     * Please note that the absolute value is taken.
     *
     * @param m
     * @param n
     *
     * @return the least common multiple
     */
    public static int lcm(int m, int n) {
        if (m < 0) {
            m = -m;
        }
        if (n < 0) {
            n = -n;
        }

        // parentheses important to avoid overflow
        return m * (n / Rational.gcd(m, n));
    }

    /**
     * Calculates the product of this with r.
     * To avoid an overflow there are first some reduction steps.
     * Please note: Cannot multiplicat two M values.
     *
     * @param r the factor
     *
     * @return the product
     */
    public Rational times(final Rational r) {

        if (r == null || r.equals(Rational.zero)) {
            return new Rational();
        }

        /*
         * (n1/d1) * (n2/d2) = (n1/d2) * (n2/d1)
         * By calling the constructors the reduction is done.
         */

        final Rational c = new Rational(this.numerator, r.denominator);
        final Rational d = new Rational(r.numerator, this.denominator);
        final Rational s = new Rational(c.numerator * d.numerator, c.denominator * d.denominator);

        if (this.m == null || this.m.equals(Rational.zero)) {
            final Rational n = new Rational(this.numerator, this.denominator);
            final Rational sm = n.times(r.m);
            return new Rational(s, sm);
        } else if (r.m == null || r.m.equals(Rational.zero)) {
            final Rational n = new Rational(r.numerator, r.denominator);
            final Rational sm = n.times(this.m);
            return new Rational(s, sm);
        } else {
            System.err.println("Two M values are used. " + "Cannot multiplicat two M values. "
                + "This is not supposed to happen in the simplex algorithm.");
            return null;
        }

    }

    /**
     * Calculates the sum of this with r.
     * To avoid an overflow there are first some reduction steps.
     *
     * @param r the summand
     * @return
     */
    public Rational plus(final Rational r) {
        // special cases
        if (r == null) {
            return this.deepcopy();
        }
        if (this.numerator == 0) {
            Rational newM = null;
            if (this.m != null) {
                newM = this.m.plus(r.m);
            } else if (r.m != null) {
                newM = r.m.deepcopy();
            }
            return new Rational(r, newM);
        }
        if (r.numerator == 0) {
            Rational newM = null;
            if (this.m != null) {
                newM = this.m.plus(r.m);
            } else if (r.m != null) {
                newM = r.m.deepcopy();
            }
            return new Rational(this, newM);
        }

        // Calculate gcd of numerators and denominators
        final int f = Rational.gcd(this.numerator, r.numerator);
        final int g = Rational.gcd(this.denominator, r.denominator);

        /*
         *  f*x     f*u     (x*u + u*y) * f
         *  ---  +  ---  =  ---------------
         *  g*y     g*v          g*y*v
         */

        final Rational s =
            new Rational((this.numerator / f) * (r.denominator / g) + (r.numerator / f) * (this.denominator / g), Rational.lcm(
                this.denominator, r.denominator));

        s.numerator *= f;

        if (this.m == null) {
            return new Rational(s, r.m);
        } else {
            final Rational newM = this.m.plus(r.m);
            return new Rational(s, newM);
        }
    }

    /**
     * Returns the negation: (-1) * this
     *
     * @return the negation
     */
    public Rational negate() {
        if (this.m == null) {
            return new Rational(-this.numerator, this.denominator);
        } else {
            return new Rational(-this.numerator, this.denominator, this.m.negate());
        }
    }

    /**
     * Calculates the difference between this and r.
     *
     * @param r the subtrahend
     *
     * @return
     */
    public Rational minus(final Rational r) {
        return this.plus(r.negate());
    }

    /**
     * returns the reciprocal (german: Kehrwert)
     * Please note: Cannot create the reciprocal when an M value is used.
     *
     * @return the reciprocal
     */
    public Rational reciprocal() {
        if (this.isM()) {
            System.err.println("A M value is used. " + "Cannot create the reciprocal of a M value. "
                + "This is not supposed to happen in the simplex algorithm.");
            return null;
        }

        return new Rational(this.denominator, this.numerator);
    }

    /**
     * Calculates the quotient of this and r.
     * Please note: Cannot divide when an M value is used.
     *
     * @param r the dividend
     *
     * @return the quotient
     */
    public Rational divideBy(final Rational r) {
        if (r.isM()) {
            System.err.println("A M value is used. " + "Cannot create the reciprocal of a M value. "
                + "This is not supposed to happen in the simplex algorithm.");
        }

        return this.times(r.reciprocal());
    }

    /**
     * Compares if this is smaller than, equal to or greater than
     * the given object and returns a negative integer, zero
     * or a positve integer.
     *
     * @param o the object to compare with
     * @return a negative integer, zero or a positve integer if it this
     *         smaller than, equal to or greater than o
     */
    @Override
    public int compareTo(final Object o) {

        if (o == null) {
            if (this.m != null && !this.m.equals(Rational.zero)) {
                return this.m.numerator;
            } else {
                return this.numerator;
            }
        }

        if (o instanceof Rational) {
            final Rational r = (Rational) o;

            int equalM;

            if (this.m == null) {
                equalM = Rational.zero.compareTo(r.m);
            } else if (r == null) {
                equalM = this.m.compareTo(Rational.zero);
            } else {
                equalM = this.m.compareTo(r.m);
            }

            if (equalM != 0) {
                return equalM;
            }

            return (this.numerator * r.denominator) - (this.denominator * r.numerator);
        }
        return 0;

    }

    public Rational getRationalPart() {
        final int dif = this.numerator % this.denominator;

        if (dif == 0) {
            return new Rational();
        }
        if (this.compareTo(Rational.zero) >= 0) {
            return new Rational(dif, this.denominator, this.m);
        } else {
            return new Rational(this.denominator + dif, this.denominator, this.m);
        }
    }

    public Rational getIntegerPart() {
        final int dif = this.numerator % this.denominator;

        if (this.compareTo(Rational.zero) >= 0) {
            return new Rational(this.numerator - dif, this.denominator, this.m);
        } else {
            return new Rational(this.numerator - this.denominator - dif, this.denominator, this.m);
        }
    }

    /**
     * @return true iff the value is bigger than 0
     */
    public boolean isPositive() {
        return this.compareTo(Rational.zero) > 0;
    }

    @Override
    public String export(final Export_Util eu) {
        // Do the same what toString() does!
        final StringBuilder sb = new StringBuilder();
        if (this.m != null && !(this.m.equals(Rational.zero))) {
            sb.append(eu.escape("M"));
            sb.append(eu.multSign());
            sb.append(this.m.export(eu));
            sb.append(eu.escape(" + "));
        }

        if (this.numerator == 0) {
            sb.append(eu.escape("0"));
        } else if (this.denominator == 1) {
            if (this.numerator < 0) {
                sb.append(eu.escape("("));
            }
            sb.append(eu.escape("" + this.numerator));
            if (this.numerator < 0) {
                sb.append(eu.escape(")"));
            }
        } else {
            sb.append(eu.fraction("" + this.numerator, "" + this.denominator));
        }

        return sb.toString();
    }
}
