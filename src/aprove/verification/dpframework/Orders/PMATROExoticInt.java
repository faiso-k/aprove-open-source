package aprove.verification.dpframework.Orders;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.PMATRO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.PolyMatrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * A matrix ordering for exotic matrices.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PMATROExoticInt<T extends ExoticInt<T>> extends PMATRO<T> {

    /**
     * @param inter
     * @param factoryParam
     * @param inner
     * @param outer
     * @param coeffOrderParam
     */
    public PMATROExoticInt(
            final AbstractPolyMatrixInterpretation<T> inter,
            final OrderPolyFactory<T> factoryParam,
            final FlatteningVisitor<T, GPolyVar> inner,
            final FlatteningVisitor<GPoly<T, GPolyVar>, GPolyVar> outer,
            final CoeffOrder<T> coeffOrderParam) {
        super(inter, factoryParam, inner, outer, coeffOrderParam);
    }

    @Override
    protected boolean constraintFulfilled(
            final PolyMatrix<T> leftMatrix,
            final PolyMatrix<T> rightMatrix,
            final ConstraintType ct) {
        if (Globals.useAssertions) {
            assert(leftMatrix.numRows() == rightMatrix.numRows()
                    && leftMatrix.numCols() == rightMatrix.numCols());
        }
        for (int i = 0; i < leftMatrix.numRows(); i++) {
            for (int j = 0; j < leftMatrix.numCols(); j++) {
                if (!this.constraintFulfilled(leftMatrix.at(i, j),
                        rightMatrix.at(i, j), ct)) {
                    return false;
                }
            }
        }
        return true;
    }

    @Override
    protected boolean constraintFulfilled(
            final OrderPoly<T> left,
            final OrderPoly<T> right,
            final ConstraintType ct) {

        Semiring<T> ringC = this.fvInner.getRingC();
        Semiring<GPoly<T, GPolyVar>> polyRing = this.fvOuter.getRingC();
        CMonoid<GMonomial<GPolyVar>> monoid = this.fvInner.getMonoid();

        // we are interested in the coefficients for x, y, ... of the
        // polynomial, so flatten it first
        this.fvOuter.applyTo(left);
        this.fvOuter.applyTo(right);

        Map<GMonomial<GPolyVar>, GPoly<T, GPolyVar>> leftMonomials =
            left.getMonomials(polyRing, monoid);
        Map<GMonomial<GPolyVar>, GPoly<T, GPolyVar>> rightMonomials =
            right.getMonomials(polyRing, monoid);
        for (Map.Entry<GMonomial<GPolyVar>, GPoly<T, GPolyVar>> entry
                : leftMonomials.entrySet()) {
            // Unlike in the natural case, here all coefficients on the left
            // have to be strictly greater than their right counterparts.
            GPoly<T, GPolyVar> leftCoeff = entry.getValue();
            // the absolute value of the coefficient is relevant, so
            // flatten it
            this.fvInner.applyTo(leftCoeff);
            T leftConst = leftCoeff.getConstantPart(ringC, monoid);

            T rightConst;
            if (!rightMonomials.containsKey(entry.getKey())) {
                rightConst = ringC.zero();
            } else {
                GPoly<T, GPolyVar> rightCoeff = rightMonomials.get(entry.getKey());
                if (rightCoeff != null) {
                    this.fvInner.applyTo(rightCoeff);
                    rightConst = rightCoeff.getConstantPart(ringC, monoid);
                } else {
                    rightConst = ringC.one();
                }
            }

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
        }

        for (Map.Entry<GMonomial<GPolyVar>, GPoly<T, GPolyVar>> entry
                : rightMonomials.entrySet()) {

            if (!leftMonomials.containsKey(entry.getKey())) {
                // unmatched entry found on rhs
                // note: for arctic numbers, 0 > 0 is correct!
                GPoly<T, GPolyVar> rightCoeff = entry.getValue();
                this.fvInner.applyTo(rightCoeff);
                T rightConst = rightCoeff.getConstantPart(ringC, monoid);
                if (this.coeffOrder.isGreater(rightConst, ringC.zero())) {
                    return false;
                }
            }
        }

        // no conflicting coefficient was found, so this constraint is fulfilled
        return true;
    }

}
