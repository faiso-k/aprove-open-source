/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * A ConstraintVisitor can be used to visit and modify a constraint with its
 * subconstraints. By calling this.applyTo(someConstraint) the constraint will
 * feed itself and all its subconstraints back to the visitor which then can
 * check the constraint or create a modification of it.
 * @param <C> The type of the coefficients used in the polynomials.
 * @author cotto
 */
public interface ConstraintVisitor<C extends GPolyCoeff> {
    /**
     * A false node is being visited.
     * @param param The constraint.
     * @return Some new constraint.
     */
    OrderPolyConstraint<C> caseFalse(OPCFalse<C> param);

    /**
     * A true node is being visited.
     * @param param The constraint.
     * @return Some new constraint.
     */
    OrderPolyConstraint<C> caseTrue(OPCTrue<C> param);

    /**
     * A logical variable node is being visited.
     * @param param The constraint.
     * @return param itself.
     */
    OrderPolyConstraint<C> caseLogVar(OPCLogVar<C> param);

    /**
     * A comment node is being visited
     *
     * @param param the constraint
     * @param comment the (new?) comment
     * @param sub the (new?) subconstraint
     * @return
     */
    OrderPolyConstraint<C> caseComment(OPCComment<C> param, String comment, OrderPolyConstraint<C> sub);

    /**
     * A not node is being visited.
     * @param param the constraint.
     * @param newConstraint the new subconstraint.
     * @return some new constraint.
     */
    OrderPolyConstraint<C> caseNot(
            OPCNot<C> param, OrderPolyConstraint<C> newConstraint);

    /**
     * A false node is being visited.
     * @param param The constraint.
     */
    void fcaseFalse(OPCFalse<C> param);

    /**
     * A true node is being visited.
     * @param param The constraint.
     */

    void fcaseTrue(OPCTrue<C> param);

    /**
     * A logical variable node is being visited.
     * @param param The constraint.
     */
    void fcaseLogVar(OPCLogVar<C> param);

    /**
     * A comment node is being visited.
     * @param param The constraint.
     */
    public void fcaseComment(final OPCComment<C> param);

    /**
     * A not node is being visited.
     * @param param the constraint.
     */
    void fcaseNot(OPCNot<C> param);

    /**
     * An existential quantifier constraint is being visited.
     * @param param The constraint.
     * @param newConstraint The (new?) subconstraint.
     * @return Some new constraint.
     */
    OrderPolyConstraint<C> caseQuantifierE(
            OPCQuantifierE<C> param,
            OrderPolyConstraint<C> newConstraint);

    /**
     * A universal quantifier constraint is being visited.
     * @param param The constraint.
     * @param newConstraint The (new?) subconstraint.
     * @return Some new constraint.
     */
    OrderPolyConstraint<C> caseQuantifierA(
            OPCQuantifierA<C> param,
            OrderPolyConstraint<C> newConstraint);

    /**
     * An and constraint is being visited.
     * @param param The constraint.
     * @param newOperands The set of (new?) subconstraints.
     * @return Some new constraint.
     */
    OrderPolyConstraint<C> caseAnd(
            OPCAnd<C> param,
            Set<OrderPolyConstraint<C>> newOperands);

    /**
     * An or constraint is being visited.
     * @param param The constraint.
     * @param newOperands The set of (new?) subconstraints.
     * @return Some new constraint.
     */
    OrderPolyConstraint<C> caseOr(
            OPCOr<C> param,
            Set<OrderPolyConstraint<C>> newOperands);

    /**
     * An atom is being visited.
     * @param param The constraint.
     * @return Some new constraint.
     */
    OrderPolyConstraint<C> caseAtom(OPCAtom<C> param);

    /**
     * An existential quantifier constraint is being visited.
     * @param param The constraint.
     */
    void fcaseQuantifierE(OPCQuantifierE<C> param);

    /**
     * A universal quantifier constraint is being visited.
     * @param param The constraint.
     */
    void fcaseQuantifierA(OPCQuantifierA<C> param);

    /**
     * An and constraint is being visited.
     * @param param The constraint.
     */
    void fcaseAnd(OPCAnd<C> param);

    /**
     * An or constraint is being visited.
     * @param param The constraint.
     */
    void fcaseOr(OPCOr<C> param);

    /**
     * An atom is being visited.
     * @param param The constraint.
     */
    void fcaseAtom(OPCAtom<C> param);

    /**
     * Start visiting the given constraint and clean up afterwards.
     * @param constraint The constraint that should be visited.
     * @return Some new constraint.
     */
    OrderPolyConstraint<C> applyToWithCleanup(OrderPolyConstraint<C> constraint);

    /**
     * Start visiting the given constraint.
     * @param constraint The constraint that should be visited.
     * @return Some new constraint.
     */
    OrderPolyConstraint<C> applyTo(OrderPolyConstraint<C> constraint);

    /**
     * Provide default implementations which basically do nothing.
     * @author cotto
     * @param <C> The type of the coefficients used in the polynomials.
     */
    public abstract class ConstraintVisitorSkeleton<C extends GPolyCoeff>
        implements ConstraintVisitor<C> {
        /**
         * Visit the given constraint (without cleanup, only use during
         * recursive visiting process, e.g. internally).
         * @param constraint The constraint to be visited.
         * @return Some new constraint.
         */
        @Override
        public OrderPolyConstraint<C> applyTo(
                final OrderPolyConstraint<C> constraint) {
            return constraint.visit(this);
        }

        /**
         * Start visiting the given constraint and clean up afterwards (use this
         * from the outside!).
         * @param constraint The constraint that should be visited.
         * @return Some new constraint.
         */
        @Override
        public OrderPolyConstraint<C> applyToWithCleanup(final OrderPolyConstraint<C> constraint) {
            return this.applyTo(constraint);
        }

        /**
         * An atom is being visited.
         * @param param The constraint.
         */
        @Override
        public void fcaseAtom(final OPCAtom<C> param) {
            return;
        }

        /**
         * An existential quantifier constraint is being visited.
         * @param param The constraint.
         * @param newConstraint The (new?) subconstraint.
         * @return Some new constraint.
         */
        @Override
        public OrderPolyConstraint<C> caseQuantifierE(
                final OPCQuantifierE<C> param,
                final OrderPolyConstraint<C> newConstraint) {
            return new OPCQuantifierE<C>(newConstraint,
                    param.getQuantifiedVariables());
        }
        /**
         * A universal quantifier constraint is being visited.
         * @param param The constraint.
         * @param newConstraint The (new?) subconstraint.
         * @return Some new constraint.
         */
        @Override
        public OrderPolyConstraint<C> caseQuantifierA(
                final OPCQuantifierA<C> param,
                final OrderPolyConstraint<C> newConstraint) {
            return new OPCQuantifierA<C>(newConstraint,
                    param.getQuantifiedVariables());
        }

        /**
         * An and constraint is being visited.
         * @param param The constraint.
         * @param newOperands The set of (new?) subconstraints.
         * @return Some new constraint.
         */
        @Override
        public OrderPolyConstraint<C> caseAnd(
                final OPCAnd<C> param,
                final Set<OrderPolyConstraint<C>> newOperands) {
            if (newOperands.size() == 1) {
                return newOperands.iterator().next();
            } else {
                return new OPCAnd<C>(newOperands);
            }
        }

        /**
         * An or constraint is being visited.
         * @param param The constraint.
         * @param newOperands The set of (new?) left subconstraints.
         * @return Some new constraint.
         */
        @Override
        public OrderPolyConstraint<C> caseOr(
                final OPCOr<C> param,
                final Set<OrderPolyConstraint<C>> newOperands) {
            if (newOperands.size() == 1) {
                return newOperands.iterator().next();
            } else {
                return new OPCOr<C>(newOperands);
            }
        }

        /**
         * An atom is being visited.
         * @param param The constraint.
         * @return Some new constraint.
         */
        @Override
        public OrderPolyConstraint<C> caseAtom(final OPCAtom<C> param) {
            return param;
        }

        /**
         * A true node is being visited.
         * @param param The constraint.
         * @return param itself.
         */
        @Override
        public OrderPolyConstraint<C> caseTrue(final OPCTrue<C> param) {
            return param;
        }

        /**
         * A logical variable node is being visited.
         * @param param The constraint.
         * @return param itself.
         */
        @Override
        public OrderPolyConstraint<C> caseLogVar(final OPCLogVar<C> param) {
            return param;
        }

        /**
         * A false node is being visited.
         * @param param The constraint.
         * @return param itself.
         */
        @Override
        public OrderPolyConstraint<C> caseFalse(final OPCFalse<C> param) {
            return param;
        }

        @Override
        public OrderPolyConstraint<C> caseComment(OPCComment<C> param,
                String comment, OrderPolyConstraint<C> sub) {
            return param;
        }

        /**
         * A not not is being visited.
         * @param param the constraint
         * @param newConstraint the new subconstraint.
         * @return param itself.
         */
        @Override
        public OrderPolyConstraint<C> caseNot(final OPCNot<C> param,
                final OrderPolyConstraint<C> newConstraint) {
            return param;
        }

        /**
         * An existential quantifier constraint is being visited.
         * @param param The constraint.
         */
        @Override
        public void fcaseQuantifierE(final OPCQuantifierE<C> param) { }

        /**
         * A universal quantifier constraint is being visited.
         * @param param The constraint.
         */
        @Override
        public void fcaseQuantifierA(final OPCQuantifierA<C> param) { }

        /**
         * An and constraint is being visited.
         * @param param The constraint.
         */
        @Override
        public void fcaseAnd(final OPCAnd<C> param) { }

        /**
         * An or constraint is being visited.
         * @param param The constraint.
         */
        @Override
        public void fcaseOr(final OPCOr<C> param) { }

        /**
         * A true node is being visited.
         * @param param The constraint.
         */
        @Override
        public void fcaseTrue(final OPCTrue<C> param) { }

        /**
         * A logical variable node is being visited.
         * @param param The constraint.
         */
        @Override
        public void fcaseLogVar(OPCLogVar<C> param) {
            throw new UnsupportedOperationException("OPCLogVar not yet supported");
        }

        /**
         * A comment node is being visited.
         * @param param The constraint.
         */
        @Override
        public void fcaseComment(final OPCComment<C> param) { }

        /**
         * A false node is being visited.
         * @param param The constraint.
         */
        @Override
        public void fcaseFalse(final OPCFalse<C> param) { }

        /**
         * A not not is being visited.
         * @param param the constraint
         */
        @Override
        public void fcaseNot(final OPCNot<C> param) { }
    }
}
