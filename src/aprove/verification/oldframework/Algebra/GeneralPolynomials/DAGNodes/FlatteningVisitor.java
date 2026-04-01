/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.util.*;

import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A FlatteningVisitor ensures that the GPoly that is being visited contains
 * itself in flat representation.
 * @author cotto
 * @version $Id$
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public class FlatteningVisitor<C extends GPolyCoeff, V extends GPolyVar>
    extends GPolyVisitor<C, V> {
    /**
     * A (semi)ring that can operate on coefficients of type C.
     */
    private final Semiring<C> ringC;

    /**
     * This monoid is used to multiply monomials.
     */
    private final CMonoid<GMonomial<V>> monoid;

    /**
     * This ring is used to work on flat GPolys.
     */
    private final GPolyFlatRing<C, V> gPolyFlatRing;

    /**
     * This pair will be used as index for several maps.
     */
    private final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair;

    /**
     * Build a FlatteningVisitor that operates based on the given rings and the
     * monoid.
     * @param polyRingParam A (semi)ring for flat polynomials.
     */
    public FlatteningVisitor(
            final GPolyFlatRing<C, V> polyRingParam) {
        this.gPolyFlatRing = polyRingParam;
        this.ringC = polyRingParam.getRing();
        this.monoid = polyRingParam.getMonoid();
        this.pair =
            new Pair<Semiring<C>, CMonoid<GMonomial<V>>>(this.ringC, this.monoid);
    }

    /**
     * @return the ring used to operate on the coefficients of type C.
     */
    public Semiring<C> getRingC() {
        return this.ringC;
    }

    /**
     * @return the monoid used to operate on the monomials over V.
     */
    public CMonoid<GMonomial<V>> getMonoid() {
        return this.monoid;
    }

    /**
     * @return the ring used to operate on flat polynomials.
     */
    public GPolyFlatRing<C, V> getGPolyFlatRing() {
        return this.gPolyFlatRing;
    }

    /**
     * A concat node consists of a coeff node and a variable part. To get the
     * flat representation one only has to merge these elements.
     * Take care of the ConcatNode which does not contain anything, this has to
     * be handled as the 1 element of any ring.
     * @param c Some ConcatNode.
     * @return c which now has a flat representation for the given rings.
     */
    @Override
    public ConcatNode<C, V> caseConcatNode(final ConcatNode<C, V> c) {
        if (!c.isFlat(this.pair)) {
            C coeff = c.getCoeff();
            VarPartNode<V> var = c.getVarPartNode();
            if (coeff == null && var == null) {
                // this ConcatNode represents 1
                c.putMonomials(this.pair,
                        ImmutableCreator.create(this.gPolyFlatRing.one()));
                return c;
            }
            // test if the tree behind this variable part node is already
            // flattened
            GMonomial<V> mon;
            if (var.hasMonomial(this.monoid)) {
                mon = var.getMonomial(this.monoid);
            } else {
                // calculate the monomial
                VariableCollector<V> vc =
                    new VariableCollector<V>(this.monoid);
                vc.applyTo(var);
                mon = vc.getMonomial();
            }
            if (coeff == null) {
                coeff = this.ringC.one();
            }
            if (coeff.equals(this.ringC.zero())) {
                Map<GMonomial<V>, C> map =
                    Collections.singletonMap(this.monoid.neutral(),
                            this.ringC.zero());
                c.putMonomials(this.pair, ImmutableCreator.create(map));
            } else {
                Map<GMonomial<V>, C> map = new LinkedHashMap<GMonomial<V>, C>(1);
                map.put(mon, coeff);
                if (!this.monoid.neutral().equals(mon)) {
                    map.put(this.monoid.neutral(), this.ringC.zero());
                }
                c.putMonomials(this.pair, ImmutableCreator.create(map));
            }
        }
        return c;
    }

    /**
     * Add the two children of the PlusNode using the given polynomial ring.
     * @param p The PlusNode being visited.
     * @param left The possibly new left child.
     * @param right The possibly new right child.
     * @return p with flat representation.
     */
    @Override
    public PlusNode<C, V> casePlusNode(
            final PlusNode<C, V> p,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        if (!p.isFlat(this.pair)) {
            Map<GMonomial<V>, C> map = this.gPolyFlatRing.plus(
                        left.getMonomials(this.ringC, this.monoid),
                        right.getMonomials(this.ringC, this.monoid));
            p.putMonomials(this.pair, ImmutableCreator.create(map));
        }
        return p;
    }

    /**
     * Subtract the two children of the MinusNode using the given polynomial
     * ring.
     * @param m The MinusNode being visited.
     * @param left The possibly new left child.
     * @param right The possibly new right child.
     * @return m with flat representation.
     */
    @Override
    public MinusNode<C, V> caseMinusNode(
            final MinusNode<C, V> m,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        if (m.getLeft().equals(m.getRight())) { // to handle zeroes ([1] - [1]) in semi-rings
            if (!m.isFlat(this.pair)) {
                Map<GMonomial<V>, C> map =
                    Collections.singletonMap(this.monoid.neutral(),
                            this.ringC.zero());
                m.putMonomials(this.pair, ImmutableCreator.create(map));
            }
            return m;
        }
        if (!this.gPolyFlatRing.isRing()) {
            throw new UnsupportedOperationException("Flattening minus nodes only works on actual rings.");
        }
        if (!m.isFlat(this.pair)) {
            GPolyFlatRing<C, V> polyRing = (GPolyFlatRing<C, V>)this.gPolyFlatRing;
            Map<GMonomial<V>, C> map = polyRing.minus(
                        left.getMonomials(this.ringC, this.monoid),
                        right.getMonomials(this.ringC, this.monoid));
            m.putMonomials(this.pair, ImmutableCreator.create(map));
        }
        return m;
    }

    /**
     * Multiply the two children of the TimesNode using the given polynomial
     * ring.
     * @param t The TimesNode being visited.
     * @param left The possibly new left child.
     * @param right The possibly new right child.
     * @return t with flat representation.
     */
    @Override
    public TimesNode<C, V> caseTimesNode(
            final TimesNode<C, V> t,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        if (!t.isFlat(this.pair)) {
            Map<GMonomial<V>, C> map = this.gPolyFlatRing.times(
                    left.getMonomials(this.ringC, this.monoid),
                    right.getMonomials(this.ringC, this.monoid));
            t.putMonomials(this.pair, ImmutableCreator.create(map));
        }
        return t;
    }
}
