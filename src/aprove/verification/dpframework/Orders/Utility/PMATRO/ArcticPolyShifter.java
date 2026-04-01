package aprove.verification.dpframework.Orders.Utility.PMATRO;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;

/**
 * "Shifts" an arctic polynomial p by some value n such that the
 * result is equivalent to n*p, while eliminating any negative
 * numbers occurring in the polynomial.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public abstract class ArcticPolyShifter<C extends GPolyCoeff, V extends GPolyVar> extends GPolyVisitor<C, V> {

    /**
     * A factory to synthesize polynomials.
     */
    protected final GPolyFactory<C, V> polyFactory;

    public ArcticPolyShifter(final GPolyFactory<C, V> polyFactory) {
        this.polyFactory = polyFactory;
    }

    @Override
    public GPoly<C, V> casePlusNode(
            final PlusNode<C, V> p,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        return this.polyFactory.plus(left, right);
    }

    @Override
    public GPoly<C, V> caseMinusNode(
            final MinusNode<C, V> m,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        return this.polyFactory.minus(left, right);
    }

    @Override
    public GPoly<C, V> caseTimesNode(
            final TimesNode<C, V> t,
            final GPoly<C , V>left,
            final GPoly<C, V> right) {
        return this.polyFactory.times(left, right);
    }

    /**
     * An ArcticPolyShifter for outer polynomials.
     */
    public static class OuterShifter<T extends ExoticInt<T>> extends ArcticPolyShifter<GPoly<T, GPolyVar>, GPolyVar> {

        /**
         * The offset to shift by.
         */
        private final int offset;

        /**
         * A shifter for inner polynomials.
         */
        private final InnerShifter<T> innerPolyShifter;

        /**
         * A factory for inner polynomials.
         */
        private final GPolyFactory<T, GPolyVar> innerPolyFactory;

        /**
         * A factory for exotic integers.
         */
        private final ExoticIntFactory<T> intFactory;

        /**
         * A map containing the minimum offsets required to eliminate all
         * negative numbers from the occurring polynomials.
         */
        private final Map<GPoly<GPoly<T, GPolyVar>, GPolyVar>, Integer> requiredOffsets;

        // fcase at every node: pop my own offset (from above),
        // push the offsets that I compute for my children
        // (depending on my type)
        private Stack<Integer> offsetStack;

        // fcase at every node:
        // overhead = own offset - offsets consumed by children
        // push(overhead)
        // case at every node: pop(overhead)
        private Stack<Integer> overheadStack;

        /**
         * Create a new shifter for arctic polynomials.
         * @param offset The value which the polys should be shifted by.
         * @param requiredOffsets A map containing, for each node in the
         * polynomial DAG, the minimum value it must be shifted by to
         * eliminate all negative numbers in it. (Use an OffsetVisitor
         * to obtain one.)
         * @param outerFactory A factory for outer polynomials.
         * @param innerFactory A factory for inner polynomials.
         * @param intFactory A factory for exotic integers.
         */
        public OuterShifter(
                final int offset,
                final Map<GPoly<GPoly<T, GPolyVar>, GPolyVar>, Integer> requiredOffsets,
                final GPolyFactory<GPoly<T, GPolyVar>, GPolyVar> outerFactory,
                final GPolyFactory<T, GPolyVar> innerFactory,
                final ExoticIntFactory<T> intFactory) {

            super(outerFactory);
            this.offset = offset;
            this.requiredOffsets = requiredOffsets;
            this.innerPolyFactory = innerFactory;
            this.intFactory = intFactory;
            this.innerPolyShifter = new InnerShifter<T>(innerFactory, intFactory);
            this.offsetStack = new Stack<Integer>();
            this.offsetStack.push(offset); // read also by fcase, hence needs init content
            this.overheadStack = new Stack<Integer>();
        }

        @Override
        public GPoly<GPoly<T, GPolyVar>, GPolyVar> caseConcatNode(
                final ConcatNode<GPoly<T, GPolyVar>, GPolyVar> node) {

            int offset = this.offsetStack.pop();
            GPoly<T, GPolyVar> coeffPoly = node.getCoeff();
            GPoly<T, GPolyVar> shiftedCoeffPoly;
            if (offset == 0) {
                return node;
            } else if (coeffPoly == null) {
                shiftedCoeffPoly = this.innerPolyFactory.buildFromCoeff(
                        this.intFactory.create(offset));
            } else {
                this.innerPolyShifter.setOffset(offset);
                shiftedCoeffPoly = coeffPoly.visit(this.innerPolyShifter);
            }
            return this.polyFactory.concat(shiftedCoeffPoly, node.getVarPartNode());
        }

        @Override
        public void fcasePlusNode(
                final PlusNode<GPoly<T, GPolyVar>, GPolyVar> node) {

            // Both children of a Plus node are shifted by the total offset.
            // first recover my offset ...
            int offset = this.offsetStack.pop();
            int leftRequired = this.requiredOffsets.get(node.getLeft());
            int rightRequired = this.requiredOffsets.get(node.getRight());
            int maxRequired = Math.max(leftRequired, rightRequired);

            // ... my children only get as much offset as needed
            this.offsetStack.push(maxRequired);
            this.offsetStack.push(maxRequired);

            int overhead = offset - maxRequired;
            if (Globals.useAssertions) {
                assert overhead >= 0 : "Total shift (" + this.offset +
                    ") insufficient for terms requiring "
                    + leftRequired + " / " + rightRequired;
            }
            // push overhead for my own future use
            this.overheadStack.push(overhead);
        }

        @Override
        public GPoly<GPoly<T, GPolyVar>, GPolyVar> casePlusNode(
                final PlusNode<GPoly<T, GPolyVar>, GPolyVar> p,
                final GPoly<GPoly<T, GPolyVar>, GPolyVar> left,
                final GPoly<GPoly<T, GPolyVar>, GPolyVar> right) {
            GPoly<GPoly<T, GPolyVar>, GPolyVar> result = this.polyFactory.plus(left, right);

            // recover overhead
            int overhead = this.overheadStack.pop();
            if (overhead > 0) {
                T exoticOverhead = this.intFactory.create(overhead);
                GPoly<T, GPolyVar> overheadPoly =
                    this.innerPolyFactory.buildFromCoeff(exoticOverhead);
                GPoly<GPoly<T, GPolyVar>, GPolyVar> overheadOuterPoly =
                    this.polyFactory.buildFromCoeff(overheadPoly);
                result = this.polyFactory.times(overheadOuterPoly, result);
            }
            return result;
        }

        @Override
        public void fcaseTimesNode(
                final TimesNode<GPoly<T, GPolyVar>, GPolyVar> node) {

            // For a Times node, the total offset is distributed over the children.
            // first recover the offset ...
            int offset = this.offsetStack.pop();
            int leftRequired = this.requiredOffsets.get(node.getLeft());
            int rightRequired = this.requiredOffsets.get(node.getRight());

            // ... the offset for the children is just as much as needs be
            this.offsetStack.push(rightRequired);
            this.offsetStack.push(leftRequired);


            int overhead = offset - (leftRequired + rightRequired);
            if (Globals.useAssertions) {
                assert overhead >= 0 : "Total shift (" + this.offset +
                    ") insufficient for terms requiring " +
                    leftRequired + " + " + rightRequired;
;
                if (! (overhead >= 0)) {
                    throw new RuntimeException(Integer.toString(overhead));
                }
            }
            // push overhead for my own future use
            this.overheadStack.push(overhead);
        }

        @Override
        public GPoly<GPoly<T, GPolyVar>, GPolyVar> caseTimesNode(
                final TimesNode<GPoly<T, GPolyVar>, GPolyVar> p,
                final GPoly<GPoly<T, GPolyVar>, GPolyVar> left,
                final GPoly<GPoly<T, GPolyVar>, GPolyVar> right) {
            GPoly<GPoly<T, GPolyVar>, GPolyVar> result = this.polyFactory.times(left, right);
            int overhead = this.overheadStack.pop();
            if (overhead > 0) {
                T exoticOverhead = this.intFactory.create(overhead);
                GPoly<T, GPolyVar> overheadPoly =
                    this.innerPolyFactory.buildFromCoeff(exoticOverhead);
                GPoly<GPoly<T, GPolyVar>, GPolyVar> overheadOuterPoly =
                    this.polyFactory.buildFromCoeff(overheadPoly);
                result = this.polyFactory.times(overheadOuterPoly, result);
            }
            return result;
        }
    }


    public class InnerShifter<T extends ExoticInt<T>> extends ArcticPolyShifter<T, GPolyVar> {

        private int offset;

        private ExoticIntFactory<T> intFactory;

        public InnerShifter(
                final GPolyFactory<T, GPolyVar>  polyFactory,
                final ExoticIntFactory<T> intFactory) {
            super(polyFactory);
            this.intFactory = intFactory;
        }

        @Override
        public GPoly<T, GPolyVar> caseConcatNode(
                final ConcatNode<T, GPolyVar> node) {

            T coeff = node.getCoeff();
            T shiftedCoeff;
            if (coeff == null) {
                shiftedCoeff = this.intFactory.create(this.offset);
            } else {
                shiftedCoeff = this.intFactory.create(coeff.intValue() + this.offset);
            }
            return this.polyFactory.concat(shiftedCoeff, node.getVarPartNode());
        }

        public void setOffset(int offset) {
            this.offset = offset;
        }
    }
}
