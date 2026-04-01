package aprove.verification.dpframework.Orders;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.PMATRO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.PolyMatrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.xml.*;

/**
 * A polynomial ordering with matrix coefficients.
 * @param <C> The type of the coefficients used in the matrices.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PMATRO<C extends GPolyCoeff> implements QActiveOrder {

    /**
     * The interpretation defining the term order (together with the order over
     * the coefficients).
     */
    protected final AbstractPolyMatrixInterpretation<C> interpretation;

    /**
     * This factory will be used to create new OrderPolys.
     */
    protected OrderPolyFactory<C> factory;

    /**
     * A FlatteningVisitor for inner polynomials.
     */
    protected FlatteningVisitor<C, GPolyVar> fvInner;

    /**
     * A FlatteningVisitor for OrderPolys.
     */
    protected FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter;

    /**
     * Some order that can put coefficients of type C in relation to 0.
     */
    protected CoeffOrder<C> coeffOrder;

    /**
     * Create the order based on the given arguments.
     * @param inter The interpretation (specialized).
     * @param factoryParam The factory used to create new OrderPolys.
     * @param outer A FlatteningVisitor for OrderPolys.
     * @param inner A FlatteningVisitor for inner polynomials.
     * @param coeffOrderParam Some order that can put coefficients of type C in
     * relation to 0.
     */
    public PMATRO(
            final AbstractPolyMatrixInterpretation<C> inter,
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
    public AbstractPolyMatrixInterpretation<C> getInterpretation() {
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

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return this.interpretation.toCPF(doc, xmlMetaData);
    }

    @Override
    public String isCPFSupported() {
        return null;
    }


    /**
     * Determine if the QActiveCondition is fulfilled.
     * @param condition Some QActiveCondition.
     * @return true iff the QActiveCondition is fulfilled.
     */
    @Override
    public boolean checkQActiveCondition(final QActiveCondition condition) {
        return this.getInterpretation().solvesQActiveConstraint(condition, this.coeffOrder);
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
    public boolean areEquivalent(final TRSTerm t1, final TRSTerm t2)
            throws AbortionException {
        final TermPair tp = TermPair.create(t1, t2);
        // TODO extend method signature by proper Abortion
        final Abortion dummyAborter = AbortionFactory.create();
        final PolyMatrix<C> m1 = this.interpretation.interpretTerm(
                tp.getLhsInStandardRepresentation(), dummyAborter);
        final PolyMatrix<C> m2 = this.interpretation.interpretTerm(
                tp.getRhsInStandardRepresentation(), dummyAborter);
        return this.constraintFulfilled(m1, m2, ConstraintType.EQ);
    }

    /**
     * @return the factory used to create order polynomials.
     */
    protected OrderPolyFactory<C> getFactory() {
        return this.factory;
    }

    /**
     * @return the flattening visitor for the outer polynomials.
     */
    public FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> getFvOuter() {
        return this.fvOuter;
    }

    /**
     * @return the flattening visitor for the inner polynomials.
     */
    public FlatteningVisitor<C, GPolyVar> getFvInner() {
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
     * @throws AbortionException
     */
    @Override
    public boolean inRelation(final TRSTerm t1, final TRSTerm t2)
            throws AbortionException {
        final TermPair tp = TermPair.create(t1, t2);
        // TODO extend method signature by proper Abortion
        final Abortion dummyAborter = AbortionFactory.create();
        final PolyMatrix<C> p1 = this.interpretation.interpretTerm(
                tp.getLhsInStandardRepresentation(), dummyAborter);
        final PolyMatrix<C> p2 = this.interpretation.interpretTerm(
                tp.getRhsInStandardRepresentation(), dummyAborter);
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
    public boolean solves(final Constraint<TRSTerm> c) throws AbortionException {
        final TermPair tp = TermPair.create(c.getLeft(), c.getRight());
        // TODO extend method signature by proper Abortion
        final Abortion dummyAborter = AbortionFactory.create();
        final PolyMatrix<C> p1 = this.interpretation.interpretTerm(
                tp.getLhsInStandardRepresentation(), dummyAborter);
        final PolyMatrix<C> p2 = this.interpretation.interpretTerm(
                tp.getRhsInStandardRepresentation(), dummyAborter);
        if (Globals.DEBUG_ULRICHSG) {
            System.out.println("Trying to solve constraint: " + c);
            System.out.println("Left matrix: " + p1.exportFlat(this.fvInner, this.fvOuter, new PLAIN_Util()));
            System.out.println("Right matrix: " + p2.exportFlat(this.fvInner, this.fvOuter, new PLAIN_Util()));
        }
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
            throw new RuntimeException("PMATRO cannot handle constraint type "
                                       + rel + " !");
        }
        final boolean result = this.constraintFulfilled(p1, p2, type);
        if (Globals.DEBUG_ULRICHSG) {
            System.out.println(result);
        }
        return result;
    }

    /**
     * For a polynomial constraint without inner variables (existentially quantified)
     *          left REL right
     * try to find out if it is valid. This is not complete, but sound.
     * @param left The left polynomial of the constraint.
     * @param right The right polynomial of the constraint.
     * @param ct The relation.
     * @return if the constraint is fulfilled then the answer should (not must)
     * be true, false otherwise.
     */
    protected boolean constraintFulfilled(
            final OrderPoly<C> left, final OrderPoly<C> right, final ConstraintType ct) {
        final Semiring<C> ringC = this.fvInner.getRingC();
        final Semiring<GPoly<C, GPolyVar>> polyRing = this.fvOuter.getRingC();
        final CMonoid<GMonomial<GPolyVar>> monoid = this.fvInner.getMonoid();

        // we are interested in the coefficients for x, y, ... of the
        // polynomial, so flatten it first
        this.fvOuter.applyTo(left);
        this.fvOuter.applyTo(right);

        final Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> leftMonomials =
            left.getMonomials(polyRing, monoid);
        final Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> rightMonomials =
            right.getMonomials(polyRing, monoid);
        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> entry
                : leftMonomials.entrySet()) {
            final GPoly<C, GPolyVar> leftCoeff = entry.getValue();
            // the absolute value of the coefficient is relevant, so
            // flatten it
            this.fvInner.applyTo(leftCoeff);
            final C leftConst = leftCoeff.getConstantPart(ringC, monoid);

            C rightConst;
            if (!rightMonomials.containsKey(entry.getKey())) {
                rightConst = ringC.zero();
            } else {
                final GPoly<C, GPolyVar> rightCoeff = rightMonomials.get(entry.getKey());
                if (rightCoeff != null) {
                    this.fvInner.applyTo(rightCoeff);
                    rightConst = rightCoeff.getConstantPart(ringC, monoid);
                } else {
                    rightConst = ringC.one();
                }
            }

            if (entry.getKey().equals(monoid.neutral())) {
                // we are looking at the constant part, both in the outer
                // and in the inner polynomials (e.g. 1 in 0x + (0a + 1)).
                if (ct.equals(ConstraintType.GT)) {
                    if (!this.coeffOrder.isGreater(leftConst, rightConst)) {
                        return false;
                    }
                } else if (ct.equals(ConstraintType.GE)) {
                    if (!this.coeffOrder.isGreaterOrEqual(leftConst, rightConst)) {
                        return false;
                    }
                } else if (ct.equals(ConstraintType.EQ)) {
                    if (!this.coeffOrder.equal(leftConst, rightConst)) {
                        return false;
                    }
                } else { // unknown constraint type
                    assert(false) : ct;
                }
            } else {
                // we are looking at some coefficient that is not the
                // innermost constant part
                if (ct.equals(ConstraintType.GT) || ct.equals(ConstraintType.GE)) {
                    if (!this.coeffOrder.isGreaterOrEqual(leftConst, rightConst)) {
                        return false;
                    }
                } else if (ct.equals(ConstraintType.EQ)) {
                    if (!this.coeffOrder.equal(leftConst, rightConst)) {
                        return false;
                    }
                } else {
                    assert(false) : ct;
                }
            }
        }

        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> entry
                : rightMonomials.entrySet()) {
            final GMonomial<GPolyVar> monomial = entry.getKey();
            if (!leftMonomials.containsKey(monomial)) {
                // unmatched entry found on rhs, but its coeff may be 0
                final C leftConst = ringC.zero(); // need not be the smallest element!
                ConstraintType ctToUse;
                if (ct != ConstraintType.GT || monomial.equals(monoid.neutral())) {
                    ctToUse = ct;
                } else {
                    // GE is enough for coeff of var for overall GT
                    ctToUse = ConstraintType.GE;
                }

                final GPoly<C, GPolyVar> rightCoeff = entry.getValue();
                this.fvInner.applyTo(rightCoeff);
                final C rightConst = rightCoeff.getConstantPart(ringC, monoid);
                switch (ctToUse) {
                case GT :
                    if (! this.coeffOrder.isGreater(leftConst, rightConst)) {
                        return false;
                    }
                    break;
                case GE :
                    if (! this.coeffOrder.isGreaterOrEqual(leftConst, rightConst)) {
                        return false;
                    }
                    break;
                case EQ :
                    if (! this.coeffOrder.equal(leftConst, rightConst)) {
                        return false;
                    }
                    break;
                default :
                    throw new RuntimeException("Unknown constraint type " + ctToUse + "!");
                }
            }
        }

        // no conflicting coefficient was found, so this constraint is fulfilled
        return true;
    }

    /**
     * For a polynomial constraint "left REL right", try to determine whether
     * it is fulfilled under the given order by pairwise comparison of
     * coefficients. This is also sound, but not complete.
     * @param leftMatrix The left side of the constraint.
     * @param rightMatrix The right side of the constraint.
     * @param ct The type of REL.
     * @return
     */
    protected boolean constraintFulfilled(
            final PolyMatrix<C> leftMatrix,
            final PolyMatrix<C> rightMatrix,
            final ConstraintType ct) {
        if (Globals.useAssertions) {
            assert(leftMatrix.numRows() == rightMatrix.numRows()
                    && leftMatrix.numCols() == rightMatrix.numCols());
        }
        for (int i = 0; i < leftMatrix.numRows(); i++) {
            for (int j = 0; j < leftMatrix.numCols(); j++) {
                if (ct.equals(ConstraintType.GT) && (i != 0 || j != 0)) {
                    if (!this.constraintFulfilled(leftMatrix.at(i, j),
                            rightMatrix.at(i, j), ConstraintType.GE)) {
                        return false;
                    }
                } else {
                    if (!this.constraintFulfilled(leftMatrix.at(i, j),
                            rightMatrix.at(i, j), ct)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

}
