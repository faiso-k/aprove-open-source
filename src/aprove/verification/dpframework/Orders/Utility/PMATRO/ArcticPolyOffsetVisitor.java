package aprove.verification.dpframework.Orders.Utility.PMATRO;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;

/**
 * Determines the value by which a polynomial over possibly negative
 * arctic numbers has to be "shifted" in order to eliminate all
 * negative numbers inside. See ArcticPolyShifter for how the
 * actual shifting is done.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public abstract class ArcticPolyOffsetVisitor<C extends GPolyCoeff, V extends GPolyVar> extends GPolyVisitor<C, V> {

    /**
     * Keeps track of which sub-polynomials require which offsets.
     */
    protected Map<GPoly<C, V>, Integer> offsets;

    /**
     * Keeps track of the maximum offset required by any visited nodes.
     * When finished, contains the offset required for the whole poly.
     */
    protected int totalOffset = 0;

    public ArcticPolyOffsetVisitor() {
        this.offsets = new LinkedHashMap<GPoly<C, V>, Integer>();
    }

    @Override
    public GPoly<C, V> casePlusNode(
            final PlusNode<C, V> node,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {

        if (Globals.useAssertions) {
            assert(this.offsets.containsKey(node.getLeft())) :
                "No offset found for " + node.getLeft() + "("
                + node.getLeft().getClass().getSimpleName() + ")";
            assert(this.offsets.containsKey(node.getRight())) :
                "No offset found for " + node.getRight() + "("
                + node.getRight().getClass().getSimpleName() + ")";
        }
        int leftOffset = this.offsets.get(node.getLeft());
        int rightOffset = this.offsets.get(node.getRight());
        int total = Math.max(leftOffset, rightOffset);
        this.totalOffset = Math.max(this.totalOffset, total);
        this.offsets.put(node, total);
        return node;
    }

    @Override
    public GPoly<C, V> caseMinusNode(
            final MinusNode<C, V> node,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {

        if (Globals.useAssertions) {
            assert(this.offsets.containsKey(node.getLeft())) :
                "No offset found for " + node.getLeft() + "("
                + node.getLeft().getClass().getSimpleName() + ")";
            assert(this.offsets.containsKey(node.getRight())) :
                "No offset found for " + node.getRight() + "("
                + node.getRight().getClass().getSimpleName() + ")";
        }
        int leftOffset = this.offsets.get(node.getLeft());
        int rightOffset = this.offsets.get(node.getRight());
        int total = leftOffset + rightOffset;
        this.totalOffset = Math.max(this.totalOffset, total);
        this.offsets.put(node, total);
        return node;
    }

    @Override
    public GPoly<C, V> caseTimesNode(
            final TimesNode<C, V> node,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {

        if (Globals.useAssertions) {
            assert(this.offsets.containsKey(node.getLeft())) :
                "No offset found for " + node.getLeft() + "("
                + node.getLeft().getClass().getSimpleName() + ")";
        }
        int leftOffset = this.offsets.get(node.getLeft());
        if (this.offsets.containsKey(node.getRight())) {
            int rightOffset = this.offsets.get(node.getRight());
            int total = leftOffset + rightOffset;
            this.totalOffset = Math.max(this.totalOffset, total);
            this.offsets.put(node, total);
        } else {
            this.offsets.put(node, leftOffset);
        }
        return node;
    }

    /**
     * Returns the least offset that the last visited polynomial has to be
     * shifted by in order to eliminate all negative numbers in it.
     *
     * CAUTION: Always use reset() before any subsequent applications of
     * the same visitor.
     */
    public int getOffset() {
        return this.totalOffset;
    }

    /**
     * Returns the map that holds the offsets required by any sub-polys
     * occurring in the last visited polynomial.
     */
    public Map<GPoly<C, V>, Integer> getOffsetMap() {
        return this.offsets;
    }

    /**
     * Reset the visitor's internal state.
     * You must always call this before applying a visitor that has
     * been used previously.
     */
    public void reset() {
        this.offsets = new LinkedHashMap<GPoly<C, V>, Integer>();
        this.totalOffset = 0;
    }

    /**
     * Return an offset visitor for arctic polynomials.
     */
    @SuppressWarnings("unchecked")
    public static <T extends ExoticInt<T>> OuterVisitor<T> getVisitor() {
        return new OuterVisitor<T>();
    }


    /**
     * An ArcticPolyOffsetVisitor for outer polynomials.
     */
    public static class OuterVisitor<T extends ExoticInt<T>>
            extends ArcticPolyOffsetVisitor<GPoly<T, GPolyVar>, GPolyVar> {

        private final InnerVisitor<T> innerVisitor;

        public OuterVisitor() {

            super();
            this.innerVisitor = new InnerVisitor<T>();
        }

        @Override
        public GPoly<GPoly<T, GPolyVar>, GPolyVar> caseConcatNode(
                final ConcatNode<GPoly<T, GPolyVar>, GPolyVar> node) {

            int offset;
            GPoly<T, GPolyVar> coeffPoly = node.getCoeff();
            if (coeffPoly == null) {
                offset = 0;
            } else {
                this.innerVisitor.reset();
                coeffPoly.visit(this.innerVisitor);
                offset = this.innerVisitor.getOffset();
            }
            this.totalOffset = offset;
            this.offsets.put(node, offset);
            return node;
        }
    }

    /**
     * An ArcticPolyOffsetVisitor for inner polynomials.
     */
    public class InnerVisitor<T extends ExoticInt<T>> extends ArcticPolyOffsetVisitor<T, GPolyVar> {

        @Override
        public GPoly<T, GPolyVar> caseConcatNode(
                final ConcatNode<T, GPolyVar> node) {

            int offset;
            T coeff = node.getCoeff();
            if (coeff == null || coeff.isPositive()) {
                offset = 0;
            } else {
                offset = coeff.abs().intValue();
            }
            this.totalOffset = Math.max(this.totalOffset, offset);
            this.offsets.put(node, offset);
            return node;
        }
    }
}
