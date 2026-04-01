/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.xml.*;

/**
 * @author cotto
 * @param <C> The type of the coefficients used in the polynomials.
 */
public abstract class GPOLO<C extends GPolyCoeff> implements QActiveOrder {
    /**
     * The interpretation defining the term order (together with the order over
     * the coefficients).
     */
    protected final GInterpretation<C> interpretation;

    /**
     * This factory will be used to create new OrderPolys.
     */
    private final OrderPolyFactory<C> factory;

    /**
     * A FlatteningVisitor for inner polynomials.
     */
    private final FlatteningVisitor<C, GPolyVar> fvInner;

    /**
     * A FlatteningVisitor for OrderPolys.
     */
    private final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter;

    /**
     * Some order that can put coefficients of type C in relation to 0.
     */
    private final CoeffOrder<C> coeffOrder;

    /**
     * Create the order based on the given arguments.
     * @param inter The interpretation (specialized).
     * @param factoryParam The factory used to create new OrderPolys.
     * @param outer A FlatteningVisitor for OrderPolys.
     * @param inner A FlatteningVisitor for inner polynomials.
     * @param coeffOrderParam Some order that can put coefficients of type C in
     * relation to 0.
     */
    public GPOLO(
            final GInterpretation<C> inter,
            final OrderPolyFactory<C> factoryParam,
            final FlatteningVisitor<C, GPolyVar> inner,
            final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> outer,
            final CoeffOrder<C> coeffOrderParam) {
        this.interpretation = inter;
        this.factory = factoryParam;
        this.fvInner = inner;
        this.fvOuter = outer;
        this.coeffOrder = coeffOrderParam;
    }

    /**
     * @return the interpretation on which this is based
     */
    public GInterpretation<C> getInterpretation() {
        return this.interpretation;
    }

    /**
     * @return the string representation of the interpretation.
     */
    @Override
    public String toString() {
        return this.interpretation.toString();
    }

    /**
     * Export the interpretation using the given export util.
     * @param eu Some export util.
     * @return the string representation of the interpretation.
     */
    @Override
    public String export(final Export_Util eu) {
        return this.interpretation.export(eu);
    }

    /**
     * Determine if the QActiveCondition is fulfilled.
     * @param condition Some QActiveCondition.
     * @return true iff the QActiveCondition is fulfilled.
     */
    @Override
    public boolean checkQActiveCondition(final QActiveCondition condition) {
        return this.getInterpretation().solvesQActiveConstraint(condition);
    }

    /**
     * Checks whether Pol(t1) = Pol(t2) in the polynomial interpretation on
     * which this is based. This is sound, but not complete.
     *
     * @param t1 first term
     * @param t2 second term
     * @return whether Pol(t1) = Pol(t2) in the underlying polynomial
     *  interpretation of this
     */
    @Override
    public boolean areEquivalent(final TRSTerm t1, final TRSTerm t2) throws AbortionException {
        final TermPair tp = TermPair.create(t1, t2);
        // TODO extend method signature by proper Abortion
        final Abortion dummyAborter = AbortionFactory.create();
        final OrderPoly<C> p1 = this.interpretation.interpretTerm(
                tp.getLhsInStandardRepresentation(), dummyAborter);
        final OrderPoly<C> p2 = this.interpretation.interpretTerm(
                tp.getRhsInStandardRepresentation(), dummyAborter);
        // OrderPoly<C> pDiff = this.factory.minus(p2, p1);
        return this.constraintFulfilled(p1, p2, ConstraintType.EQ);
    }

    /**
     * @return the factury used to create order polynomials.
     */
    protected OrderPolyFactory<C> getFactory() {
        return this.factory;
    }

    /**
     * @return the flattening visitor for the outer polynomials.
     */
    protected FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> getFvOuter() {
        return this.fvOuter;
    }

    /**
     * @return the flattening visitor for the inner polynomials.
     */
    protected FlatteningVisitor<C, GPolyVar> getFvInner() {
        return this.fvInner;
    }

    /**
     * Returns whether Pol(t1) > Pol(t2) according to the used interpretation
     * of function symbols. This is sound, but not complete.
     *
     * @param t1 first term
     * @param t2 second term
     * @return whether Pol(t1) > Pol(t2) holds given the current
     *  interpretation for function symbols
     */
    @Override
    public boolean inRelation(final TRSTerm t1, final TRSTerm t2)
        throws AbortionException {
        final TermPair tp = TermPair.create(t1, t2);
        // TODO extend method signature by proper Abortion
        final Abortion dummyAborter = AbortionFactory.create();
        final OrderPoly<C> p1 = this.interpretation.interpretTerm(
                tp.getLhsInStandardRepresentation(), dummyAborter);
        final OrderPoly<C> p2 = this.interpretation.interpretTerm(
                tp.getRhsInStandardRepresentation(), dummyAborter);
        // OrderPoly<C> pDiff = this.factory.minus(p1, p2);
        return this.constraintFulfilled(p1, p2, ConstraintType.GT);
    }

    /**
     * Checks whether this solves <code>c</code>. This is sound, but not
     * complete.
     *
     * @param c the term constraint to check
     * @return <code>true</code> if constraint lies in the polynomial
     *         ordering, <code>false</code> otherwise
     */
    @Override
    public boolean solves(final Constraint<TRSTerm> c)
    throws AbortionException {
        OrderPoly<C> p1, p2;
        final OrderPoly<C> pDiff;
        final TermPair tp = TermPair.create(c.getLeft(), c.getRight());
        // TODO extend method signature by proper Abortion
        final Abortion dummyAborter = AbortionFactory.create();
        p1 = this.interpretation.interpretTerm(
                tp.getLhsInStandardRepresentation(), dummyAborter);
        p2 = this.interpretation.interpretTerm(
                tp.getRhsInStandardRepresentation(), dummyAborter);
        // pDiff = this.factory.minus(p1, p2);
        final OrderRelation rel = c.getType();
        ConstraintType type;
        switch (rel) {
        case EQ :
            type = ConstraintType.EQ;
            break;
        case GE :
            type = ConstraintType.GE;
            break;
        case GR :
            type = ConstraintType.GT;
            break;
        default:
            throw new RuntimeException("GPOLO cannot handle constraint type "
                                       + rel + " !");
        }
        return this.constraintFulfilled(p1, p2, type);
    }

    /**
     * For every constraint without inner variables (existentially quantified)
     *          poly REL 0
     * try to find out if it is valid. This is not complete, but sound.
     * @param poly The polynomial of the constraint.
     * @param ct The relation to 0.
     * @return if the constraint is fulfilled then the answer should (not must)
     * be true, false otherwise.
     */
    protected boolean constraintFulfilled(
            final OrderPoly<C> poly, final ConstraintType ct) {
        if (!this.fvInner.getRingC().isRing() || !this.fvOuter.getRingC().isRing()) {
            throw new UnsupportedOperationException("This version of GPOLO::constraintsFulfilled() works only on actual rings.");
        }
        final Ring<C> ring = (Ring<C>)this.fvInner.getRingC();
        final Ring<GPoly<C, GPolyVar>> polyRing = (Ring<GPoly<C, GPolyVar>>)this.fvOuter.getRingC();
        final CMonoid<GMonomial<GPolyVar>> monoid = this.fvInner.getMonoid();

        // we are interested in the coefficients for x, y, ... of the
        // polynomial, so flatten it first
        this.fvOuter.applyTo(poly);

        final Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> map =
            poly.getMonomials(polyRing, monoid);
        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> entry
                : map.entrySet()) {
            final GPoly<C, GPolyVar> coeff = entry.getValue();
            // the absolute value of the coefficient is relevant, so
            // flatten it
            this.fvInner.applyTo(coeff);
            final C constant = coeff.getConstantPart(ring, monoid);
            final int signum = this.coeffOrder.signum(constant);
            if (entry.getKey().equals(monoid.neutral())) {
                // we are looking at the constant part, both in the outer
                // and in the inner polynomial (e.g. 1 in 0x + (0a + 1)).

                if (ct.equals(ConstraintType.GT)) {
                    // for poly > 0 the constant part must be > 0
                    if (signum <= 0) {
                        // this is not the case, so return false
                        return false;
                    } // otherwise check the other coefficients
                } else if (ct.equals(ConstraintType.EQ)) {
                    // all coefficients must be 0.
                    if (signum != 0) {
                        return false;
                    }
                } else if (ct.equals(ConstraintType.GE)) {
                    // a negative constant part is not good here
                    if (signum < 0) {
                        return false;
                    }
                } else {
                    return false;
                }
            } else {
                // we are looking at some coefficient that is not the
                // innermost constant part

                if (ct.equals(ConstraintType.GT)) {
                    if (signum < 0) {
                        // -x + 1 > 0
                        return false;
                    }
                } else if (ct.equals(ConstraintType.EQ)) {
                    if (signum != 0) {
                        // 2x + 0 = 0
                        return false;
                    }
                } else if (ct.equals(ConstraintType.GE)) {
                    if (signum < 0) {
                        // -x + 0 >= 0
                        return false;
                    }
                } else {
                    return false;
                }
            }
        }
        // no conflicting coefficient was found, so this constraint is fulfilled
        return true;
    }

    /**
     * For a polynomial constraint "left REL right", try to determine whether
     * it is fulfilled under the given order by pairwise comparison of
     * coefficients. Use for non-subtractable coefficients (i.e. those not
     * on actual rings) where the standard version of the absolute positiveness
     * criterion cannot be applied. This is also sound, but not complete.
     * @param leftPoly The left side of the constraint.
     * @param rightPoly The right side of the constraint.
     * @param ct The type of REL.
     * @return
     */
    protected boolean constraintFulfilled(
            final OrderPoly<C> leftPoly, final OrderPoly<C> rightPoly,
            final ConstraintType ct) {
        final Semiring<C> ring = this.fvInner.getRingC();
        final Semiring<GPoly<C, GPolyVar>> polyRing = this.fvOuter.getRingC();
        final CMonoid<GMonomial<GPolyVar>> monoid = this.fvInner.getMonoid();

        // we are interested in the coefficients for x, y, ... of the
        // polynomials, so flatten them first
        this.fvOuter.applyTo(leftPoly);
        this.fvOuter.applyTo(rightPoly);

        final Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> leftMonomials =
            leftPoly.getMonomials(polyRing, monoid);
        final Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> rightMonomials =
            rightPoly.getMonomials(polyRing, monoid);
        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> leftEntry
                : leftMonomials.entrySet()) {
            final GPoly<C, GPolyVar> leftCoeff = leftEntry.getValue();
            // the absolute value of the coefficient is relevant, so
            // flatten it
            this.fvInner.applyTo(leftCoeff);
            final C leftConstant = leftCoeff.getConstantPart(ring, monoid);
            final GPoly<C, GPolyVar> rightCoeff = rightMonomials.get(leftEntry.getKey());

            if (rightCoeff == null) {
                if (ct.equals(ConstraintType.EQ) && !leftConstant.equals(ring.zero())) {
                    return false;
                }
            } else {
                this.fvInner.applyTo(rightCoeff);
                final C rightConstant = rightCoeff.getConstantPart(ring, monoid);

                if (leftEntry.getKey().equals(monoid.neutral())) {  // constant part
                    if (ct.equals(ConstraintType.GT)) {
                        if (!this.coeffOrder.isGreater(leftConstant, rightConstant)) {
                            return false;
                        }
                    } else if (ct.equals(ConstraintType.GE)) {
                        if (!this.coeffOrder.isGreaterOrEqual(leftConstant, rightConstant)) {
                            return false;
                        }
                    } else if (ct.equals(ConstraintType.EQ)) {
                        if (!this.coeffOrder.equal(leftConstant, rightConstant)) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                } else {    // non-constant monomial
                    if (ct.equals(ConstraintType.GT) || ct.equals(ConstraintType.GE)) {
                        if (!this.coeffOrder.isGreaterOrEqual(leftConstant, rightConstant)) {
                            return false;
                        }
                    } else if (ct.equals(ConstraintType.EQ)) {
                        if (!this.coeffOrder.equal(leftConstant, rightConstant)) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
            }
        }

        // Check whether there is an unmatched, non-zero entry on the rhs
        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> rightEntry
                : rightMonomials.entrySet()) {
            final GPoly<C, GPolyVar> leftCoeff = leftMonomials.get(rightEntry.getKey());
            if (leftCoeff == null) {
                final GPoly<C, GPolyVar> rightCoeff = rightEntry.getValue();
                this.fvInner.applyTo(rightCoeff);
                final C constant = rightCoeff.getConstantPart(ring, monoid);

                // For the current monomial, we have no information on the left
                // hand side (leftCoeff == null), but some a*X on the right
                // hand side (where X is some varpart node, e.g. x^2).
                // At this position we already know that X is not the neutral
                // element, so X != 1 (the constant part always exists on both
                // sides).
                // For lhs EQ rhs it is okay to have a*X on the right hand side,
                // if a = 0.
                // For lhs GT rhs and lhs GE rhs it is okay to have a*X on the
                // right hand side if a <= 0.
                if (ct.equals(ConstraintType.EQ)) {
                    if (!constant.equals(ring.zero())) {
                        return false;
                    }
                } else {
                    if (!this.coeffOrder.isGreaterOrEqual(ring.zero(), constant)) {
                        return false;
                    }
                }
            }
        }
        // no conflicting coefficient was found, so this constraint is fulfilled
        return true;
    }

    /**
     * creates the domain element within a CPF interpretation
     */
    protected abstract Element toCPFDomain(Document doc, final XMLMetaData xmlMetaData);

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return this.interpretation.toCPF(doc, xmlMetaData, this.toCPFDomain(doc, xmlMetaData));
    }

    @Override
    public String isCPFSupported() {
        return null;
    }

}
