/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A GPoly is a node that not only contains a variable part or a coefficient,
 * but both. So "x" is no valid GPolynomial, but "1 o x" is (where o
 * concatenates coefficients and variable parts).
 * In contrast to polynomials created by Carsten Fuhs, the current
 * implementation of this interface does not store the mathematical polynomial
 * in unique (flat) representation, but as a DAG of operations defining the
 * polynomial.
 * So (a+b)*(a+b) is different (as in "not ==" and of course "!equals()") from
 * a*a + 2ab + b*b. Because of this there is no equals() and no hashCode().
 * In order to be able to actually compute with polynomials, there is a reserved
 * place for the flat representation. This may not be computed at all, which
 * might be useful for polynomials representing coefficients of some outer
 * polynomial.
 * Because every GPoly is defined through operations and not the results of
 * these operations, it is possible to construct one GPoly (using some term
 * interpretation?) and get several flat representations using different rings
 * and monoids. So depending on the definition of "+" the GPoly 1+2 may result
 * in 3, but may also result in 1 if 2 is the neutral element ("0") of "+".
 * The implementation built around this interface was designed with
 * commutative coefficients in mind. When flattening the polynomial ax*by the
 * result will be (a*b)(x*y). So if dealing with, e.g., matrices the result of
 * ax*by might differ from (a*b)(x*y) when inserting specific values for
 * x and y.
 * @author cotto
 * @version $Id$
 *
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public interface GPoly<C extends GPolyCoeff, V extends GPolyVar> extends VisitableGPoly<C, V>, GPolyCoeff {
    /**
     * Find out if the polynomial is already calculated and exists in flat
     * representation. Because the ring over coefficients and the monoid over
     * variable parts determine the result of the calculation, one has to
     * provide a ring and monoid here.
     * @param ringC The semiring over coefficients of type C.
     * @param monoid The monoid over monomials over variables of type V.
     * @return true iff the polynomial exists in flat form for the given ring
     * and monoid.
     */
    boolean isFlat(Semiring<C> ringC, CMonoid<GMonomial<V>> monoid);

    /**
     * Convenience Method
     * @param pair The pair defining the ring and monoid used to flatten
     * the polynomial.
     * @return true iff the polynomial represented by this node already is
     * stored in flat representation.
     */
    boolean isFlat(final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair);

    /**
     * @return true iff the poly contains some variable.
     */
    boolean containsVariable();

    /**
     * @return the set of all variables contained in this polynomial.
     */
    ImmutableSet<V> getVariables();

    /**
     * @return true iff the poly contains a min or max node
     */
    boolean hasMaxMin();

    /**
     * @return true iff no variable occurs in the polynomial. Note that computeConstant may still return null.
     */
    boolean isConstant();

    /**
     * @return true if the polynomial represents the 1 element in some
     *  canonical way (sufficient, but not necessary condition)
     */
    boolean isOne();

    /**
     * @return true if the polynomial represents the 0 element in some
     *  canonical way (sufficient, but not necessary condition)
     */
    boolean isZero();

    /**
     * @param ringC A semiring used to operate on coefficients.
     * @param monoid A monoid used to operate on variable parts over V.
     * @return the coefficient of "1".
     */
    C getConstantPart(Semiring<C> ringC, CMonoid<GMonomial<V>> monoid);

    /**
     * @param pair A pair containing the semiring and monoid.
     * @return the coefficient of "1".
     */
    C getConstantPart(Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair);

    /**
     * @return the list of all coefficients contained in this polynomial.
     */
    ImmutableList<C> getCoeffs();

    /**
     * @return the list of all coefficients occurring in
     * this polynomial as a coefficient for a variable part containing the given
     * variable.
     * @param var Extract the coefficients that belong to some variable part
     * containing this variable.
     */
    ImmutableList<C> getCoeffs(V var);

    /**
     * @param var Extract the coefficients that belong to some variable part
     * containing this variable.
     * @param pair A pair containing a semiring used to operate on coefficients and
     * a monoid used to operate on variable parts over V
     * @return the coefficients that belong to some GMonomial containing the
     * given variable.
     */
    ImmutableList<C> getCoeffsFromMap(V var, Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair);

    /**
     * @param var Extract the coefficients that belong to some variable part
     * containing this variable.
     * @param ringC A semiring used to operate on coefficients.
     * @param monoid A monoid used to operate on variable parts over V.
     * @return the coefficients that belong to some GMonomial containing the
     * given variable.
     */
    ImmutableList<C> getCoeffsFromMap(V var, Semiring<C> ringC, CMonoid<GMonomial<V>> monoid);

    /**
     * @return some readable string representation.
     */
    @Override
    String toString();

    /**
     * In order to add or multiply two GPolys in flat representation, the
     * monomials have to be known in the GPolyRing. The result is an immutable
     * map, so the requesting object cannot break this polynomial.
     * By definition every flat GPoly has a constant part a*1 (as in x + a)
     * including the case a=0. So 1*x is not valid, but 1*x + 0*1 is.
     * Additionally apart from the constant part no coefficient is allowed to
     * be 0, so that 0*x + 1*1 is not valid.
     * @param ringC This semiring will be used to operate on coefficients.
     * @param monoid This monoid will be used to operate on
     * (variable parts of) monomials.
     * @return The monomials.
     */
    ImmutableMap<GMonomial<V>, C> getMonomials(Semiring<C> ringC, CMonoid<GMonomial<V>> monoid);

    /**
     * In order to add or multiply two GPolys in flat representation, the
     * monomials have to be known in the GPolyRing. The result is an immutable
     * map, so the requesting object cannot break this polynomial.
     * By definition every flat GPoly has a constant part a*1 (as in x + a)
     * including the case a=0. So 1*x is not valid, but 1*x + 0*1 is.
     * Additionally apart from the constant part no coefficient is allowed to
     * be 0, so that 0*x + 1*1 is not valid.
     * @param pair A pair containing the ring and the monoid.
     * @return The monomials.
     */
    ImmutableMap<GMonomial<V>, C> getMonomials(Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair);

    Map<Pair<Semiring<C>, CMonoid<GMonomial<V>>>, ImmutableMap<GMonomial<V>, C>> getMonomials();

    /**
     * Exports the polynomial.
     * @param eu the export util
     * @return the exported version of the polynomial.
     */
    @Override
    String export(Export_Util eu);

    /**
     * Exports the polynomial, uses information from the ring and monoid.
     * @param ring a semiring used to operate on coefficients of type C.
     * @param monoid a monoid used to operate on monomials over V.
     * @param eu the export util.
     * @return the exported version of the polynomial.
     */
    String exportFlat(Semiring<C> ring, CMonoid<GMonomial<V>> monoid, Export_Util eu);

    /**
     * If this polynomial represents a constant (does not contain any variable), compute the represented value using the
     * provided ring. This method may fail and return null instead.
     * @param ring the ring that works on coefficients of this polynomial
     * @return the represented constant or null
     */
    C computeConstant(Semiring<C> ring);

    /**
     * This skeleton provides the default implementation for isFlat() and
     * getMonomials(). In order to fill the map with monomials, a method
     * putMonomials() can be used.
     * @author cotto
     */

    public abstract class GPolySkeleton<C extends GPolyCoeff, V extends GPolyVar> implements GPoly<C, V> {
        /**
         * This constructor sets an empty monomials map.
         */
        public GPolySkeleton() {
            this.monomials = new HashMap<>();
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean isOne() {
            return false;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean isZero() {
            return false;
        }

        /**
         * In order to add or multiply two GPolys in flat representation, the
         * monomials have to be known in the GPolyRing. The result is an
         * immutable map, so the requesting object cannot break this polynomial.
         * By definition every flat GPoly has a constant part a*1 (as in x + a)
         * including the case a=0. So 1*x is not valid, but 1*x + 0*1 is.
         * Additionally apart from the constant part no coefficient is allowed
         * to be 0, so that 0*x + 1*1 is not valid.
         * @param ringC This semiring will be used to operate on coefficients.
         * @param monoid This monoid will be used to operate on
         * (variable parts of) monomials.
         * @return The monomials.
         */
        @Override
        public ImmutableMap<GMonomial<V>, C> getMonomials(final Semiring<C> ringC, final CMonoid<GMonomial<V>> monoid) {
            final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair = new Pair<>(ringC, monoid);
            if (Globals.useAssertions) {
                assert (this.isFlat(ringC, monoid)) : "You have to flatten this polynomial first!";
            }
            return this.monomials.get(pair);
        }

        /**
         * In order to add or multiply two GPolys in flat representation, the
         * monomials have to be known in the GPolyRing. The result is an
         * immutable map, so the requesting object cannot break this polynomial.
         * By definition every flat GPoly has a constant part a*1 (as in x + a)
         * including the case a=0. So 1*x is not valid, but 1*x + 0*1 is.
         * Additionally apart from the constant part no coefficient is allowed
         * to be 0, so that 0*x + 1*1 is not valid.
         * @param pair A pair containing the ring and monoid.
         * @return The monomials.
         */
        @Override
        public ImmutableMap<GMonomial<V>, C> getMonomials(final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair) {
            if (Globals.useAssertions) {
                assert (this.isFlat(pair)) : "You have to flatten this polynomial first!";
            }
            return this.monomials.get(pair);
        }

        /**
         * Required by OrderPoly for XML export.
         */
        @Override
        public Map<Pair<Semiring<C>, CMonoid<GMonomial<V>>>, ImmutableMap<GMonomial<V>, C>> getMonomials() {
            return this.monomials;
        }

        /**
         * @param var Extract the coefficients that belong to some variable part
         * containing this variable.
         * @param ringC A semiring used to operate on coefficients.
         * @param monoid A monoid used to operate on variable parts over V.
         * @return the coefficients that belong to some GMonomial containing the
         * given variable.
         */
        @Override
        public ImmutableList<C> getCoeffsFromMap(final V var,
            final Semiring<C> ringC,
            final CMonoid<GMonomial<V>> monoid) {
            return this.getCoeffsFromMap(var, new Pair<>(ringC, monoid));
        }

        /**
         * @param var Extract the coefficients that belong to some variable part
         * containing this variable.
         * @param pair A pair containing a semiring used to operate on coefficients and
         * a monoid used to operate on variable parts over V
         * @return the coefficients that belong to some GMonomial containing the
         * given variable.
         */
        @Override
        public ImmutableList<C> getCoeffsFromMap(final V var, final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair) {
            final List<C> result = new ArrayList<>();
            for (final Map.Entry<GMonomial<V>, C> entry : this.getMonomials(pair).entrySet()) {
                if (entry.getKey().getExponents().containsKey(var)) {
                    result.add(entry.getValue());
                }
            }
            return ImmutableCreator.create(result);
        }

        /**
         * @param ringC A semiring used to operate on coefficients.
         * @param monoid A monoid used to operate on variable parts over V.
         * @return the coefficient of "1".
         */
        @Override
        public C getConstantPart(final Semiring<C> ringC, final CMonoid<GMonomial<V>> monoid) {
            final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair = new Pair<>(ringC, monoid);
            if (Globals.useAssertions) {
                assert (this.isFlat(pair));
            }
            C result = this.monomials.get(pair).get(monoid.neutral());
            if (result == null) {
                result = ringC.zero();
            }
            return result;
        }

        /**
         * @param pair A pair defining the semiring and monoid used to operate on
         * coefficients and monomials.
         * @return the coefficient of "1".
         */
        @Override
        public C getConstantPart(final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair) {
            if (Globals.useAssertions) {
                assert (this.isFlat(pair));
            }
            C result = this.monomials.get(pair).get(pair.y.neutral());
            if (result == null) {
                result = pair.x.zero();
            }
            return result;
        }

        /**
         * @return true iff no variable occurs in the polynomial.
         */
        @Override
        public boolean isConstant() {
            return this.getVariables().size() == 0;
        }

        /**
         * A flat polynomial is a sum of monomials. Store this data using a map
         * from the variable part to the corresponding coefficient.
         * 2x^2 + (3+a)xy + 4 is represented as x^2 -> 2, xy -> 3+a, 1 -> 4.
         */
        private final Map<Pair<Semiring<C>, CMonoid<GMonomial<V>>>, ImmutableMap<GMonomial<V>, C>> monomials;

        /**
         * Put some value in the monomial map storing the flat representations.
         * @param pair The semiring and monoid that were used to calculate the
         * representation.
         * @param map The map giving the polynomial in flat representation.
         */
        protected void putMonomials(final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair,
            final ImmutableMap<GMonomial<V>, C> map) {
            if (Globals.useAssertions) {
                assert (this.monomials.get(pair) == null) : "Why did you compute this again?";
                assert (map.containsKey(pair.y.neutral())) : "Every GPoly must have some constant part.";
            }
            this.monomials.put(pair, map);
        }

        /**
         * @param ringC Some semiring over coefficients of type C.
         * @param monoid Some monoid over monomials over variables of type V.
         * @return true iff the polynomial represented by this node already is
         * stored in flat representation.
         */
        @Override
        public boolean isFlat(final Semiring<C> ringC, final CMonoid<GMonomial<V>> monoid) {
            final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair = new Pair<>(ringC, monoid);
            return this.monomials.containsKey(pair);
        }

        /**
         * @param pair The pair defining the ring and monoid used to flatten
         * the polynomial.
         * @return true iff the polynomial represented by this node already is
         * stored in flat representation.
         */
        @Override
        public boolean isFlat(final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair) {
            return this.monomials.containsKey(pair);
        }

        /**
         * @return a string representation.
         */
        @Override
        public String toString() {
            String result;
            if ((Globals.DEBUG_CKUKNAT || Globals.DEBUG_COTTO) && this.monomials.size() == 1) {
                // technically the string representation should not show the
                // (only) flat version, but this is useful for debugging.
                final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair = this.monomials.keySet().iterator().next();
                result = this.exportFlat(pair.x, pair.y, new PLAIN_Util());
            } else {
                result = this.export(new PLAIN_Util());
            }
            return result;
        }

        /**
         * Exports the polynomial, uses information from the ring and monoid.
         * @param ring a semiring used to operate on coefficients of type C.
         * @param monoid a monoid used to operate on monomials over V.
         * @param eu the export util.
         * @return the exported version of the polynomial.
         */
        @Override
        public String exportFlat(final Semiring<C> ring, final CMonoid<GMonomial<V>> monoid, final Export_Util eu) {
            final Map<GMonomial<V>, C> map = this.getMonomials(ring, monoid);
            final StringBuilder sb = new StringBuilder();
            boolean first = true;
            String start = "";
            for (final Map.Entry<GMonomial<V>, C> entry : map.entrySet()) {
                final String varString = entry.getKey().toString();
                final C coeff = entry.getValue();
                if (!coeff.equals(ring.zero())) {
                    start = "";
                    String coeffString = "";
                    if (!coeff.equals(ring.one()) || varString.length() == 0) {
                        if ((Globals.DEBUG_CKUKNAT || Globals.DEBUG_COTTO) && this.monomials.size() == 1) {
                            coeffString = coeff.toString();
                        } else {
                            coeffString = coeff.export(eu);
                        }
                    }
                    if (varString.length() > 0 && coeffString.length() > 0) {
                        coeffString = "(" + coeffString + ")";
                    }
                    if (!first) {
                        sb.append(" + ");
                    }
                    first = false;
                    sb.append(coeffString);
                    sb.append(varString);
                } else if (first && varString.length() == 0) {
                    start = coeff.export(eu);
                }
            }
            if (map.size() == 0) {
                return "0";
            }
            return start + sb.toString();
        }

    }
}
