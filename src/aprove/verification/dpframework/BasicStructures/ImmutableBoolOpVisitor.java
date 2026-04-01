/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.BasicStructures;

import immutables.*;

/** Visitor for ImmutableBoolOp<T>.
 *
 * <p>An boolean formula can be interpreted as a tree, where each boolean
 * operation is an inner node and each atom is a leaf node. For each node
 * type TYPE, there are up to three methods:</p>
 *
 * <ul>
 * <li><code>inTYPE</code> - called on entering the node</li>
 * <li><code>midTYPE</code> - called between two calls to child nodes</li>
 * <li><code>outTYPE</code> - called on leaving the node</li>
 * </ul>
 *
 * <p>On entering a node, the corresponding in*-Method is called, then
 * <code>apply</code> is called for each child. Between two such calls,
 * the mid*-Method is called for the node. After all children are processed,
 * the node's out*-Method is called.</p>
 *
 * <p>Node types without children only have the in-Method, node types with
 * at most one child only have the in- and mid-Methods.</p>
 *
 * <p>Visiting an {@link ImmutableBoolOp} is started by calling
 * <code>apply</code>.</p>
 *
 * @author noschinski
 *
 * @param <T> Type parameter of ImmutableBoolOp
 */
public interface ImmutableBoolOpVisitor<T> {

    /** Apply the visitor.
     *
     * This is also called by the {@link ImmutableBoolOp} to apply the
     * visitor to substructures.
     *
     * @param ibo Apply the visitor to this {@link ImmutableBoolOp}.
     */
    public void apply(ImmutableBoolOp<T> ibo);

    /**
     * Callback for entering an atom.
     *
     * @param atom The atom which was entered.
     */
    public void inAtom(T atom);

    /**
     * Callback for entering a conjunction.
     *
     * @param subformulas Operands of the conjunction
     */
    public void inConjunction(ImmutableList<ImmutableBoolOp<T>> subformulas);

    /**
     * Callback between calls to children in a conjunction.
     *
     * @param subformulas Operands of the conjunction
     */
    public void midConjunction(ImmutableList<ImmutableBoolOp<T>> subformulas);

    /** Callback for leaving a conjunction.
     *
     * @param subformulas Operands of the conjunction
     */
    public void outConjunction(ImmutableList<ImmutableBoolOp<T>> subformulas);

    /**
     * Callback for entering a disjunction.
     *
     * @param subformulas Operands of the disjunction
     */
    public void inDisjunction(ImmutableList<ImmutableBoolOp<T>> subformulas);

    /**
     * Callback between calls to children in a disunction.
     *
     * @param subformulas Operands of the disjunction
     */
    public void midDisjunction(ImmutableList<ImmutableBoolOp<T>> subformulas);

    /**
     * Callback for leaving a disjunction.
     *
     * @param subformulas Operands of the disjunction
     */
    public void outDisjunction(ImmutableList<ImmutableBoolOp<T>> subformulas);

    /**
     * Callback for entering a false node.
     */

    public void inFalse();

    /**
     * Callback for entering a negation.
     *
     * @param subformula Operand of the negation
     */
    public void inNegation(ImmutableBoolOp<T> subformula);

    /**
     * Callback for leaving a negation.
     *
     * @param subformula Operand of the negation
     */
    public void outNegation(ImmutableBoolOp<T> subformula);

    /**
     * Callback for entering a false node.
     */

    public void inTrue();

    /** Minimal skeleton implementation */
    public abstract class BoolOpVisitorSkeleton<T> implements ImmutableBoolOpVisitor<T> {

        @Override
        public void apply(ImmutableBoolOp<T> ibo) {
            ibo.visit(this);
        }

        @Override
        public void inAtom(T atom) {
        }

        @Override
        public void inConjunction(ImmutableList<ImmutableBoolOp<T>> subformulas) {
        }

        @Override
        public void inDisjunction(ImmutableList<ImmutableBoolOp<T>> subformulas) {
        }

        @Override
        public void inFalse() {
        }

        @Override
        public void inNegation(ImmutableBoolOp<T> subformula) {
        }

        @Override
        public void inTrue() {
        }

        @Override
        public void midConjunction(ImmutableList<ImmutableBoolOp<T>> subformulas) {
        }

        @Override
        public void midDisjunction(ImmutableList<ImmutableBoolOp<T>> subformulas) {
        }

        @Override
        public void outConjunction(ImmutableList<ImmutableBoolOp<T>> subformulas) {
        }

        @Override
        public void outDisjunction(ImmutableList<ImmutableBoolOp<T>> subformulas) {
        }

        @Override
        public void outNegation(ImmutableBoolOp<T> subformula) {
        }

    }

    /**
     * Anonymous skeleton.
     *
     * <p>Allows an visitor which just return one value to be implemented
     * as an anonymous class. <code>start</code> is supposed to call apply
     * and return the generated value afterwards.</p>
     *
     */
    public abstract class AnonSkeleton<T, U> extends BoolOpVisitorSkeleton<T> {
        public abstract U start(ImmutableBoolOp<T> ibo);
    }

}
