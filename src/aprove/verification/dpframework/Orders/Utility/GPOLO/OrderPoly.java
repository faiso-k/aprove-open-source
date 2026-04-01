/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * This class is an abbreviation for GPoly&lt;GPoly&lt;C, Variable&gt;,
 * Variable&gt;. An OrderPoly allows to have polynomials like (a+3b+c^2+7)x^2y +
 * ... It may be used in implementations of new POLO variants, where some
 * variables are universally quantified (x,y,z), others existentially (a,b,c):
 * POL(s(x)) = ax + b and POL(s(s(x)) = ax^2 + 2b. Here "a" and "2b" are
 * coefficients of the outer polynomial with variable x. The outer coefficients
 * are polynomials over the variables a and b, where a in "a" has the
 * coefficient 1 and b in "2b" has the coefficient 2.
 *
 * @author cotto
 * @param <C> The type of the inner coefficient.
 */
public class OrderPoly<C extends GPolyCoeff> implements GPoly<GPoly<C, GPolyVar>, GPolyVar> {
    /**
     * This is the real poly.
     */
    private final GPoly<GPoly<C, GPolyVar>, GPolyVar> poly;

    /**
     * The set of all variables occurring in the coefficients of this poynomial.
     */
    private ImmutableSet<GPolyVar> innerVariables;

    /**
     * Create an OrderPoly based on the given poly.
     *
     * @param polyParam This polynomial is the real content of the OrderPoly.
     */
    public OrderPoly(final GPoly<GPoly<C, GPolyVar>, GPolyVar> polyParam) {
        this.poly = polyParam;
        this.calculateInnerVariables();
    }

    /**
     * @return all variables that occur in this polynomial, not including the
     *         variables in the coefficients.
     */
    @Override
    public ImmutableSet<GPolyVar> getVariables() {
        return this.poly.getVariables();
    }

    /**
     * @return all variables that occur in the coefficients of this polynomial.
     */
    public ImmutableSet<GPolyVar> getInnerVariables() {
        // if (this.innerVariables == null) {
        // this.calculateInnerVariables();
        // }
        return this.innerVariables;
    }

    /**
     * Calculate the set of all variables occurring in the coefficients of this
     * polynomial.
     */
    public void calculateInnerVariables() {
        final Set<GPolyVar> result = new LinkedHashSet<>();
        for (final GPoly<C, GPolyVar> coeff : this.poly.getCoeffs()) {
            if (coeff != null) {
                // coeff == null is the 1 element
                result.addAll(coeff.getVariables());
            }
        }
        this.innerVariables = ImmutableCreator.create(result);
    }

    /**
     * Wrapper.
     *
     * @param ringC (ask GPoly).
     * @param monoid (ask GPoly).
     * @return (ask GPoly).
     */
    @Override
    public ImmutableMap<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> getMonomials(final Semiring<GPoly<C, GPolyVar>> ringC,
        final CMonoid<GMonomial<GPolyVar>> monoid) {
        return this.poly.getMonomials(ringC, monoid);
    }

    /**
     * Wrapper.
     *
     * @param pair (ask GPoly).
     * @return (ask GPoly).
     */
    @Override
    public ImmutableMap<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> getMonomials(final Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> pair) {
        return this.poly.getMonomials(pair);
    }

    @Override
    public Map<Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>>, ImmutableMap<GMonomial<GPolyVar>, GPoly<C, GPolyVar>>> getMonomials() {
        return this.poly.getMonomials();
    }

    /**
     * Wrapper.
     *
     * @param ringC (ask GPoly).
     * @param monoid (ask GPoly).
     * @return (ask GPoly).
     */
    @Override
    public boolean isFlat(final Semiring<GPoly<C, GPolyVar>> ringC, final CMonoid<GMonomial<GPolyVar>> monoid) {
        return this.poly.isFlat(ringC, monoid);
    }

    /**
     * Wrapper.
     *
     * @param pair (ask GPoly).
     * @return (ask GPoly).
     */
    @Override
    public boolean isFlat(final Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> pair) {
        return this.poly.isFlat(pair);
    }

    /**
     * Wrapper.
     *
     * @param gpv (ask GPoly).
     * @return (ask GPoly).
     */
    @Override
    public GPoly<GPoly<C, GPolyVar>, GPolyVar> visit(final GPolyVisitor<GPoly<C, GPolyVar>, GPolyVar> gpv) {
        return this.poly.visit(gpv);
    }

    /**
     * @return the degree of the polynomial, i.e., the maximal degree of some
     *         monomial (where opposed to an algebraic point of view, the degree
     *         of ZERO is 0 and not -\infty)
     */
    public BigInteger getDegree() {
        BigInteger res = BigInteger.ZERO;
        for (final Entry<Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>>, ImmutableMap<GMonomial<GPolyVar>, GPoly<C, GPolyVar>>> monomial : this.getMonomials().entrySet()) {
            for (final GMonomial<GPolyVar> gmon : monomial.getValue().keySet()) {
                final BigInteger exp = gmon.getDegree();
                if (exp.compareTo(res) > 0) {
                    res = exp;
                }
            }
        }
        return res;
    }

    /**
     * @return true iff the poly contains some variable.
     */
    @Override
    public synchronized boolean containsVariable() {
        return this.getVariables().size() + this.innerVariables.size() > 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean hasMaxMin() {
        return this.poly.hasMaxMin();
    }

    /**
     * @return the list of all coefficients (which are polynomials!) occurring
     *         in this polynomial.
     */
    @Override
    public synchronized ImmutableList<GPoly<C, GPolyVar>> getCoeffs() {
        return this.poly.getCoeffs();
    }

    /**
     * @return the list of all coefficients (which are polynomials!) occurring
     *         in this polynomial as a coefficient for a variable part
     *         containing the given variable.
     * @param var Extract the coefficients that belong to some variable part
     *        containing this variable.
     */
    @Override
    public synchronized ImmutableList<GPoly<C, GPolyVar>> getCoeffs(final GPolyVar var) {
        return this.poly.getCoeffs(var);
    }

    /**
     * @return string representation.
     */
    @Override
    public String toString() {
        return this.poly.toString();
    }

    /**
     * @param ringC A semiring used to operate on coefficients.
     * @param monoid A monoid used to operate on variable parts over V.
     * @return the coefficient of "1".
     */
    @Override
    public GPoly<C, GPolyVar> getConstantPart(final Semiring<GPoly<C, GPolyVar>> ringC,
        final CMonoid<GMonomial<GPolyVar>> monoid) {
        return this.poly.getConstantPart(ringC, monoid);
    }

    /**
     * @param pair A pair containing the semiring and monoid.
     * @return the coefficient of "1".
     */
    @Override
    public GPoly<C, GPolyVar> getConstantPart(final Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> pair) {
        return this.poly.getConstantPart(pair);
    }

    /**
     * @return true iff no variable occurs in the polynomial.
     */
    @Override
    public boolean isConstant() {
        return this.poly.isConstant();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isOne() {
        return this.poly.isOne();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isZero() {
        return this.poly.isZero();
    }

    /**
     * @param var Extract the coefficients that belong to some variable part
     *        containing this variable.
     * @param ringC A semiring used to operate on coefficients.
     * @param monoid A monoid used to operate on variable parts over V.
     * @return the coefficients that belong to some GMonomial containing the
     *         given variable.
     */
    @Override
    public ImmutableList<GPoly<C, GPolyVar>> getCoeffsFromMap(final GPolyVar var,
        final Semiring<GPoly<C, GPolyVar>> ringC,
        final CMonoid<GMonomial<GPolyVar>> monoid) {
        return this.poly.getCoeffsFromMap(var, ringC, monoid);
    }

    /**
     * @param var Extract the coefficients that belong to some variable part
     *        containing this variable.
     * @param pair A pair containing a semiring used to operate on coefficients
     *        and a monoid used to operate on variable parts over V
     * @return the coefficients that belong to some GMonomial containing the
     *         given variable.
     */
    @Override
    public ImmutableList<GPoly<C, GPolyVar>> getCoeffsFromMap(final GPolyVar var,
        final Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> pair) {
        // Not yet implemented?
        throw new UnsupportedOperationException();
    }

    /**
     * If this represents an inner polynomial (of the form 1*coeff), return the
     * coeff as a GPoly. Do not use this method in any other case.
     */
    public GPoly<C, GPolyVar> getInnerPoly() {
        final List<GPoly<C, GPolyVar>> coeffs = this.poly.getCoeffs();
        if (Globals.useAssertions) {
            assert (coeffs.size() == 1);
        }
        return coeffs.get(0);
    }

    public void deepFlatten(final FlatteningVisitor<C, GPolyVar> inner,
        final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> outer) {

        this.poly.visit(outer);
        final Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monoms =
            this.poly.getMonomials(outer.getRingC(), outer.getMonoid());
        for (final GPoly<C, GPolyVar> innerPoly : monoms.values()) {
            innerPoly.visit(inner);
        }
    }

    /**
     * Return the actual GPoly wrapped inside this object.
     */
    public GPoly<GPoly<C, GPolyVar>, GPolyVar> unwrap() {
        return this.poly;
    }

    /**
     * Exports the polynomial.
     *
     * @param eu the export util
     * @return the exported version of the polynomial.
     */
    @Override
    public String export(final Export_Util eu) {
        return this.poly.export(eu);
    }

    /**
     * Exports the polynomial, uses information from the ring and monoid.
     *
     * @param ring the semiring used to operate on the inner polynomials.
     * @param monoid the monoid used to operate on monomials over variables.
     * @param eu the export util.
     * @return the exported version of the polynomial.
     */
    @Override
    public String exportFlat(final Semiring<GPoly<C, GPolyVar>> ring,
        final CMonoid<GMonomial<GPolyVar>> monoid,
        final Export_Util eu) {
        return this.poly.exportFlat(ring, monoid, eu);
    }

    /**
     * Exports the polynomial, uses information about the inner and outer ring
     * and the monoid.
     *
     * @param inner a ring that operates on coefficients of type C.
     * @param outer a ring that operates on polynomials over C and GPolyVar.
     * @param eu the export util.
     * @return the exported version of the polynomial.
     */
    public String exportFlatDeep(final FlatteningVisitor<C, GPolyVar> inner,
        final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> outer,
        final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        final Semiring<GPoly<C, GPolyVar>> polyRing = outer.getRingC();
        final Semiring<C> ring = inner.getRingC();
        final CMonoid<GMonomial<GPolyVar>> monoid = outer.getMonoid();

        // flatten the outer polynomial
        outer.applyTo(this.poly);
        boolean first = true;
        final Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> map = this.poly.getMonomials(polyRing, monoid);
        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> entry : map.entrySet()) {
            final GPoly<C, GPolyVar> coeff = entry.getValue();
            // flatten the coefficient
            inner.applyTo(coeff);
            // get the string representation of the coefficient using the ring
            // and monoid.
            String coeffString = coeff.exportFlat(ring, monoid, eu);
            String varString = entry.getKey().export(eu);
            if (coeffString.equals(inner.getRingC().zero().toString())) {
                coeffString = "";
                varString = "";
            }
            if (coeffString.equals(inner.getRingC().one().toString()) && !"".equals(varString)) {
                coeffString = "";
            }
            if (coeffString.length() + varString.length() > 0 && !first) {
                sb.append(" + ");
            }
            if (coeffString.length() + varString.length() > 0) {
                first = false;
            }
            if (!"".equals(coeffString)) {
                sb.append('[');
                sb.append(coeffString);
                sb.append(']');
            }
            sb.append(varString);
        }
        final String result = sb.toString();
        if (result.length() == 0) {
            return "0";
        } else {
            return result;
        }
    }

    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData, final Semiring<C> innerRing) {
        final FullSharingFactory<C, GPolyVar> outerFactory = new FullSharingFactory<>();
        final CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<>();
        final GPolyFlatRing<GPoly<C, GPolyVar>, GPolyVar> outerFlatRing =
            new SimpleGPolyFlatRing<>(outerFactory, monoid);
        final Semiring<GPoly<C, GPolyVar>> outerRing = outerFlatRing.getRing();
        final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter = new FlatteningVisitor<>(outerFlatRing);
        final GPolyFlatRing<C, GPolyVar> innerFlatRing = new SimpleGPolyFlatRing<>(innerRing, monoid);
        final FlatteningVisitor<C, GPolyVar> fvInner = new FlatteningVisitor<>(innerFlatRing);

        fvOuter.applyTo(this.poly);
        if (Globals.useAssertions) {
            assert (!this.getMonomials().isEmpty()) : "Polynomials must be flattened before exporting them as XML";
        }
        final Element polyTag = XMLTag.POLYNOMIAL.createElement(doc);
        final Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monoms = this.getMonomials(outerRing, monoid);
        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monomial : monoms.entrySet()) {
            final GPoly<C, GPolyVar> coeffPoly = monomial.getValue();
            fvInner.applyTo(coeffPoly);
            for (final Entry<GMonomial<GPolyVar>, C> entry : coeffPoly.getMonomials(innerRing, monoid).entrySet()) {
                assert (monoid.neutral().equals(entry.getKey()));
            }
            final C coeff = coeffPoly.getConstantPart(innerRing, monoid);
            final Element monomTag = XMLTag.MONOMIAL.createElement(doc);
            monomTag.appendChild(((XMLObligationExportable) coeff).toDOM(doc, xmlMetaData));
            final Map<GPolyVar, BigInteger> indefs = monomial.getKey().getExponents();
            for (final Map.Entry<GPolyVar, BigInteger> var : indefs.entrySet()) {
                final Element varTag = XMLTag.INDEFINIT.createElement(doc);
                varTag.appendChild(((XMLObligationExportable) var.getKey()).toDOM(doc, xmlMetaData));
                varTag.appendChild(XMLTag.createInteger(doc, var.getValue().intValue()));
                monomTag.appendChild(varTag);
            }
            polyTag.appendChild(monomTag);
        }
        return polyTag;
    }

    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData, final Semiring<C> innerRing) {
        final FullSharingFactory<C, GPolyVar> outerFactory = new FullSharingFactory<>();
        final CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<>();
        final GPolyFlatRing<GPoly<C, GPolyVar>, GPolyVar> outerFlatRing =
            new SimpleGPolyFlatRing<>(outerFactory, monoid);
        final Semiring<GPoly<C, GPolyVar>> outerRing = outerFlatRing.getRing();
        final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter = new FlatteningVisitor<>(outerFlatRing);
        final GPolyFlatRing<C, GPolyVar> innerFlatRing = new SimpleGPolyFlatRing<>(innerRing, monoid);
        final FlatteningVisitor<C, GPolyVar> fvInner = new FlatteningVisitor<>(innerFlatRing);

        fvOuter.applyTo(this.poly);
        if (Globals.useAssertions) {
            assert (!this.getMonomials().isEmpty()) : "Polynomials must be flattened before exporting them as XML";
        }
        final Element sum = CPFTag.SUM.create(doc);
        final Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monoms = this.getMonomials(outerRing, monoid);
        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monomial : monoms.entrySet()) {
            final GPoly<C, GPolyVar> coeffPoly = monomial.getValue();
            fvInner.applyTo(coeffPoly);
            for (final Entry<GMonomial<GPolyVar>, C> entry : coeffPoly.getMonomials(innerRing, monoid).entrySet()) {
                assert (monoid.neutral().equals(entry.getKey()));
            }
            final C coeff = coeffPoly.getConstantPart(innerRing, monoid);
            final Element product = CPFTag.PRODUCT.create(doc);
            product.appendChild(CPFTag.POLYNOMIAL.create(
                doc,
                CPFTag.COEFFICIENT.create(doc, ((CPFAdditional) coeff).toCPF(doc, xmlMetaData))));
            final Map<GPolyVar, BigInteger> indefs = monomial.getKey().getExponents();
            for (final Map.Entry<GPolyVar, BigInteger> var_pow : indefs.entrySet()) {
                String var_name = var_pow.getKey().getName();
                // drop x_ - prefix;
                var_name = var_name.substring(2);
                BigInteger pow = var_pow.getValue();
                while (pow.compareTo(BigInteger.ZERO) > 0) {
                    // important: the variable element must be created in every iteration
                    // since otherwise appendChild will only store one variable!
                    product.appendChild(CPFTag.POLYNOMIAL.create(doc, CPFTag.VARIABLE.create(doc, var_name)));
                    pow = pow.subtract(BigInteger.ONE);
                }
            }
            sum.appendChild(CPFTag.POLYNOMIAL.create(doc, product));
        }
        return CPFTag.POLYNOMIAL.create(doc, sum);
    }

    public static <CT extends GPolyCoeff> boolean equals(final GInterpretation<CT> interpretation,
        final GPoly<GPoly<CT, GPolyVar>, GPolyVar> p1,
        final GPoly<GPoly<CT, GPolyVar>, GPolyVar> p2) {
        if (!p1.isFlat(interpretation.getOuterRingMonoid())) {
            interpretation.getFvOuter().applyTo(p1);
        }

        if (!p2.isFlat(interpretation.getOuterRingMonoid())) {
            interpretation.getFvOuter().applyTo(p2);
        }
        final ImmutableMap<GMonomial<GPolyVar>, GPoly<CT, GPolyVar>> p1Monomials =
            p1.getMonomials(interpretation.getOuterRingMonoid());
        final ImmutableMap<GMonomial<GPolyVar>, GPoly<CT, GPolyVar>> p2Monomials =
            p2.getMonomials(interpretation.getOuterRingMonoid());
        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<CT, GPolyVar>> p1Monom : p1Monomials.entrySet()) {
            final GPoly<CT, GPolyVar> p2Coeff = p2Monomials.get(p1Monom.getKey());
            if (p2Coeff == null || !OrderPoly.innerEquals(interpretation, p1Monom.getValue(), p2Coeff)) {
                return false;
            }
        }
        return true;
    }

    public static <CT extends GPolyCoeff> boolean innerEquals(final GInterpretation<CT> interpretation,
        final GPoly<CT, GPolyVar> p1,
        final GPoly<CT, GPolyVar> p2) {
        if (!p1.isFlat(interpretation.getInnerRingMonoid())) {
            interpretation.getFvInner().applyTo(p1);
        }

        if (!p2.isFlat(interpretation.getInnerRingMonoid())) {
            interpretation.getFvInner().applyTo(p2);
        }
        return p1.getMonomials(interpretation.getInnerRingMonoid()).equals(
            p2.getMonomials(interpretation.getInnerRingMonoid()));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public GPoly<C, GPolyVar> computeConstant(final Semiring<GPoly<C, GPolyVar>> ring) {
        return this.poly.computeConstant(ring);
    }
}
