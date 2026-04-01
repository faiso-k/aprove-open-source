package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatFunctions.*;
import immutables.*;

/**
 *
 * <p>Invariants:</p>
 * <ul>
 * <li>The coefficient for every monomial is not zero.</li>
 * </ul>
 *
 * <p>Beware, this is not optimized at all.</p>
 *
 */
public final class RationalPolynomial implements Immutable, Exportable, Iterable<RationalPolynomial.Monomial> {
    private final static <K, V> Map<K, V> singletonMap(final K key, final V value) {
        Map<K, V> m = new LinkedHashMap<>();
        m.put(key, value);
        return m;
    }

    private final static Map<IndefinitePart, BigRational> emptyMap = new LinkedHashMap<>();

    public static final RationalPolynomial ZERO = RationalPolynomial.createFromBigRational(BigRational.ZERO);
    public static final RationalPolynomial ONE = RationalPolynomial.createFromBigRational(BigRational.ONE);
    public final ImmutableMap<IndefinitePart, BigRational> monomials;

    private RationalPolynomial(final ImmutableMap<IndefinitePart, BigRational> monomials) {
        if (Globals.useAssertions) {
            if (monomials.values().contains(BigRational.ZERO)) {
                assert !monomials.values().contains(BigRational.ZERO);
            }
        }
        this.monomials = monomials;
    }

    public RationalPolynomial(final Monomial mon) {
        this(ImmutableCreator.create(RationalPolynomial.singletonMap(mon.indefinitePart, mon.coefficient)));
    }

    public static RationalPolynomial createFromBigRational(final BigRational r) {
        return new RationalPolynomial(ImmutableCreator.create(BigRational.ZERO.equals(r) ? RationalPolynomial.emptyMap : RationalPolynomial.singletonMap(
            IndefinitePart.ONE,
            r)));
    }

    public RationalPolynomial create(final ImmutableMap<IndefinitePart, BigRational> monomials) {
        // TODO remove cruft from monomials
        return new RationalPolynomial(monomials);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.monomials == null ? 0 : this.monomials.hashCode());
        return result;
    }

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
        RationalPolynomial other = (RationalPolynomial) obj;
        if (this.monomials == null) {
            if (other.monomials != null) {
                return false;
            }
        } else if (!this.monomials.equals(other.monomials)) {
            return false;
        }
        return true;
    }

    /**
     * Mostly a class to make code more readable. The hope is that a "sufficient
     * intelligent compiler" will optimize it away.
     */
    public static final class Monomial implements Immutable, Exportable {
        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + (this.coefficient == null ? 0 : this.coefficient.hashCode());
            result = prime * result + (this.indefinitePart == null ? 0 : this.indefinitePart.hashCode());
            return result;
        }

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
            Monomial other = (Monomial) obj;
            if (this.coefficient == null) {
                if (other.coefficient != null) {
                    return false;
                }
            } else if (!this.coefficient.equals(other.coefficient)) {
                return false;
            }
            if (this.indefinitePart == null) {
                if (other.indefinitePart != null) {
                    return false;
                }
            } else if (!this.indefinitePart.equals(other.indefinitePart)) {
                return false;
            }
            return true;
        }

        public final BigRational coefficient;
        public final IndefinitePart indefinitePart;

        public Monomial(final BigRational coefficient, final IndefinitePart indefinitePart) {
            this.coefficient = coefficient;
            this.indefinitePart = indefinitePart;
        }

        public Monomial negate() {
            return new Monomial(this.coefficient.negate(), this.indefinitePart);
        }

        public Monomial multiply(final Monomial m) {
            LinkedHashMap<String, Integer> exponents = new LinkedHashMap<>();
            exponents.putAll(this.indefinitePart.getExponents());
            for (Entry<String, Integer> entry : m.indefinitePart.getExponents().entrySet()) {
                String var = entry.getKey();
                int exponent = exponents.containsKey(var) ? exponents.get(var) : 0;
                exponent += entry.getValue();
                exponents.put(var, exponent);
            }
            return new Monomial(this.coefficient.multiply(m.coefficient), IndefinitePart.create(exponents));
        }

        /**
         * Returns the monomial "q", such that "this = q * m" holds. Since we are
         * restricted to positive exponents, this might fail and we return null.
         * @param m
         * @return
         */
        public Monomial divide(final Monomial m) {
            ImmutableMap<String, Integer> myExps = this.indefinitePart.getExponents();
            LinkedHashMap<String, Integer> qExps = new LinkedHashMap<>();
            qExps.putAll(myExps);
            for (Entry<String, Integer> exponent : m.indefinitePart.getExponents().entrySet()) {
                String var = exponent.getKey();
                int exp = myExps.containsKey(var) ? myExps.get(var) : 0;
                exp -= exponent.getValue();
                if (exp < 0) {
                    return null;
                }
                if (exp == 0) {
                    qExps.remove(var);
                } else {
                    qExps.put(var, exp);
                }
            }
            BigRational qCoeff = this.coefficient.divide(m.coefficient);
            IndefinitePart qIndefinitePart = IndefinitePart.create(qExps);
            Monomial q = new Monomial(qCoeff, qIndefinitePart);
            if (Globals.useAssertions) {
                Monomial qm = q.multiply(m);
                assert this.equals(qm);
            }
            return q;
        }

        @Override
        public String toString() {
            return this.export(new PLAIN_Util());

        }

        public SMTLIBRatValue toSMTLIBRatValue() {
            List<SMTLIBRatValue> values = new ArrayList<>();
            if (!BigRational.ONE.equals(this.coefficient)) {
                values.add(this.coefficient.toSMTLIBRatValue());
            }
            for (Entry<String, Integer> varAndExp : this.indefinitePart.getExponents().entrySet()) {
                SMTLIBRatVariable var = SMTLIBRatVariable.create(varAndExp.getKey());
                int exp = varAndExp.getValue();
                if (exp < 0) {
                    throw new RuntimeException("Negative Exponent while exporting to SMT.");
                }
                for (int i = 0; i < exp; ++i) {
                    values.add(var);
                }
            }
            if (values.size() == 0) {
                return SMTLIBRatConstant.create(BigInteger.ONE);
            }
            if (values.size() == 1) {
                return values.get(0);
            }
            return SMTLIBRatMult.create(values);
        }

        @Override
        public String export(final Export_Util eu) {
            String rv = "";
            if (!BigRational.ONE.equals(this.coefficient)) {
                rv += this.coefficient.export(eu);
            }
            if (!this.indefinitePart.isEmpty()) {
                rv += this.indefinitePart.export(eu);
            }
            return rv.length() == 0 ? "1" : rv;
        }

        public RationalPolynomial applySubstitution(final Map<String, RationalPolynomial> subst) {
            RationalPolynomial product = RationalPolynomial.createFromBigRational(this.coefficient);
            for (Entry<String, Integer> exp : this.indefinitePart.getExponents().entrySet()) {
                String var = exp.getKey();
                if (subst.containsKey(var)) {
                    RationalPolynomial pol = subst.get(var);
                    for (int i = 0, l = exp.getValue(); i < l; ++i) {
                        product = product.multiply(pol);
                    }
                } else {
                    product = product.multiply(var);
                }
            }
            return product;
        }
    }

    @Override
    public Iterator<Monomial> iterator() {
        return new Iterator<Monomial>() {
            final Iterator<Entry<IndefinitePart, BigRational>> iterator = RationalPolynomial.this.monomials
                .entrySet()
                .iterator();

            @Override
            public boolean hasNext() {
                return this.iterator.hasNext();
            }

            @Override
            public Monomial next() {
                Entry<IndefinitePart, BigRational> next = this.iterator.next();
                return new Monomial(next.getValue(), next.getKey());
            }

            @Override
            public void remove() {
                throw new RuntimeException("Hey, I'm immutable!");
            }
        };
    }

    public RationalPolynomial multiply(final String var) {
        Map<IndefinitePart, BigRational> mons = new LinkedHashMap<>();
        for (Monomial mon : this) {
            Map<String, Integer> indef = new LinkedHashMap<>();
            indef.putAll(mon.indefinitePart.getExponents());
            int exp = 1 + (indef.containsKey(var) ? indef.get(var) : 0);
            if (exp == 0) {
                indef.remove(var);
            } else {
                indef.put(var, exp);
            }
            mons.put(IndefinitePart.create(ImmutableCreator.create(indef)), mon.coefficient);
        }
        return new RationalPolynomial(ImmutableCreator.create(mons));
    }

    public RationalPolynomial multiply(final BigRational c) {
        Map<IndefinitePart, BigRational> newMons = new LinkedHashMap<>();
        for (Entry<IndefinitePart, BigRational> m : this.monomials.entrySet()) {
            newMons.put(m.getKey(), m.getValue().multiply(c));
        }
        return new RationalPolynomial(ImmutableCreator.create(newMons));
    }

    public RationalPolynomial multiply(final Monomial m) {
        Map<IndefinitePart, BigRational> result = new LinkedHashMap<>();
        for (Monomial n : this) {
            Monomial nm = n.multiply(m);
            result.put(nm.indefinitePart, nm.coefficient);
        }
        return new RationalPolynomial(ImmutableCreator.create(result));
    }

    public RationalPolynomial multiply(final RationalPolynomial o) {
        RationalPolynomial result = RationalPolynomial.ZERO;
        for (Monomial m : o) {
            result = result.add(this.multiply(m));
        }
        return result;
    }

    public RationalPolynomial add(final RationalPolynomial o) {
        LinkedHashMap<IndefinitePart, BigRational> monomials = new LinkedHashMap<>();
        monomials.putAll(this.monomials);
        for (Monomial m : o) {
            BigRational coefficient =
                monomials.containsKey(m.indefinitePart) ? monomials.get(m.indefinitePart) : BigRational.ZERO;
            coefficient = coefficient.add(m.coefficient);
            if (BigRational.ZERO.equals(coefficient)) {
                monomials.remove(m.indefinitePart);
            } else {
                monomials.put(m.indefinitePart, coefficient);
            }
        }
        return new RationalPolynomial(ImmutableCreator.create(monomials));
    }

    public RationalPolynomial subtract(final RationalPolynomial o) {
        return this.add(o.negate());
    }

    public RationalPolynomial negate() {
        return this.multiply(BigRational.MINUSONE);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public static RationalPolynomial createMonomial(final int coefficient, final String... vars) {
        return RationalPolynomial.createMonomial(new BigRational(coefficient, 1), vars);
    }

    public static RationalPolynomial createMonomial(final BigRational coefficient, final String... vars) {

        Map<String, Integer> exponents = new LinkedHashMap<>();
        for (String s : vars) {
            int exp = exponents.containsKey(s) ? exponents.get(s) : 0;
            exponents.put(s, exp + 1);
        }
        return new RationalPolynomial(new Monomial(coefficient, IndefinitePart.create(ImmutableCreator
            .create(exponents))));
    }

    public Set<String> getVariables() {
        Set<String> rv = new LinkedHashSet<>();
        for (IndefinitePart ip : this.monomials.keySet()) {
            rv.addAll(ip.getIndefinites());
        }
        return rv;
    }

    public SMTLIBRatValue toSMTLIBRatValue() {
        List<SMTLIBRatValue> l = new ArrayList<>();
        for (Monomial m : this) {
            l.add(m.toSMTLIBRatValue());
        }
        if (l.size() == 0) {
            return SMTLIBRatConstant.create(BigInteger.ZERO);
        }
        return SMTLIBRatPlus.create(l);
    }

    @Override
    public String export(final Export_Util eu) {
        StringBuilder sb = new StringBuilder();
        for (Monomial mon : this) {
            if (sb.length() > 0) {
                if (mon.coefficient.signum() < 0) {
                    sb.append(" - ");
                    sb.append(mon.negate().toString());
                } else {
                    sb.append(" + ");
                    sb.append(mon.export(eu));
                }
            } else {
                sb.append(mon.export(eu));
            }
        }
        return sb.length() == 0 ? "0" : sb.toString();
    }

    public RationalPolynomial instantiate(final Map<String, RationalPolynomial> replacements) {
        RationalPolynomial sum = RationalPolynomial.ZERO;
        for (Monomial mon : this) {
            RationalPolynomial product = RationalPolynomial.createFromBigRational(mon.coefficient);
            for (Entry<String, Integer> entry : mon.indefinitePart.getExponents().entrySet()) {
                String var = entry.getKey();
                int exp = entry.getValue();
                RationalPolynomial value =
                    replacements.containsKey(var) ? replacements.get(var) : this.createFromVariableName(var);
                if (Globals.useAssertions) {
                    assert exp > 0;
                }
                for (int i = 0; i < exp; ++i) {
                    product = product.multiply(value);
                }
            }
            sum = sum.add(product);
        }
        return sum;
    }

    private RationalPolynomial createFromVariableName(final String var) {
        return RationalPolynomial.createMonomial(BigRational.ONE, var);
    }

    public int getMaximalPolynomialDegree() {
        int maxDegree = 0;
        for (Monomial mon : this) {
            maxDegree = Math.max(maxDegree, mon.indefinitePart.getDegree());
        }
        return maxDegree;
    }

    public int numberOfMonomials() {
        return this.monomials.size();
    }

    public static RationalPolynomial createAsSumOfMonomials(final Set<Monomial> monomials) {
        Map<IndefinitePart, BigRational> map = new LinkedHashMap<>();
        for (Monomial m : monomials) {
            IndefinitePart indef = m.indefinitePart;
            BigRational coeff = (map.containsKey(indef) ? map.get(indef) : BigRational.ZERO).add(m.coefficient);
            map.put(indef, coeff);
        }
        return new RationalPolynomial(ImmutableCreator.create(map));
    }

    public RationalPolynomial add(final Monomial mon) {
        Map<IndefinitePart, BigRational> mons = new LinkedHashMap<>();
        mons.putAll(this.monomials);
        BigRational coefficient = mon.coefficient;
        IndefinitePart indef = mon.indefinitePart;
        if (mons.containsKey(indef)) {
            coefficient = coefficient.add(mons.get(indef));
        }
        mons.put(indef, coefficient);
        return new RationalPolynomial(ImmutableCreator.create(mons));
    }

    public RationalPolynomial applySubstitution(final Map<String, RationalPolynomial> subst) {
        RationalPolynomial sum = RationalPolynomial.ZERO;
        for (Monomial mon : this) {
            sum = sum.add(mon.applySubstitution(subst));
        }
        return sum;
    }

    public Map<IndefinitePart, RationalPolynomial> split(Set<String> vars) {
        Map<IndefinitePart, RationalPolynomial> rv = new LinkedHashMap<>();
        for (Monomial m : this) {
            LinkedHashMap<String, Integer> conVars = new LinkedHashMap<>();
            LinkedHashMap<String, Integer> nonVars = new LinkedHashMap<>();

            for (Entry<String, Integer> e : m.indefinitePart.getExponents().entrySet()) {
                String v = e.getKey();
                Integer exp = e.getValue();
                if (vars.contains(v)) {
                    conVars.put(v, exp);
                } else {
                    nonVars.put(v, exp);
                }

            }
            IndefinitePart nonIP = IndefinitePart.create(nonVars);
            RationalPolynomial curr = rv.get(nonIP);
            if (curr == null) {
                curr = RationalPolynomial.ZERO;
            }
            RationalPolynomial added =
                RationalPolynomial.createFromMonomial(new Monomial(m.coefficient, IndefinitePart.create(conVars)));
            curr = curr.add(added);
            rv.put(nonIP, curr);
        }
        return rv;
    }

    private static RationalPolynomial createFromMonomial(Monomial monomial) {
        Map<IndefinitePart, BigRational> mons = new LinkedHashMap<>();
        mons.put(monomial.indefinitePart, monomial.coefficient);
        return new RationalPolynomial(ImmutableCreator.create(mons));
    }

    public boolean isLinearOnVars(Set<String> vars) {
        for (Monomial m : this) {
            int degree = 0;
            for (Entry<String, Integer> e : m.indefinitePart.getExponents().entrySet()) {
                if (!vars.contains(e.getKey())) {
                    degree += e.getValue();
                }
            }
            if (degree > 1) {
                return false;
            }
        }
        return true;
    }

    public static RationalPolynomial createVarPower(String var, int power) {
        assert power >= 0;
        return RationalPolynomial.createFromMonomial(new Monomial(BigRational.ONE, IndefinitePart.create(var, power)));
    }
}
