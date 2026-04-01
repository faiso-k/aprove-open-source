/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class InfRuleConstraintRepl<D extends Object> extends InfRule {

    static enum Mode {
        SingleStep, Full;
    }

    private final Mode mode;

    public InfRuleConstraintRepl(final Mode mode) {
        this.mode = mode;
    }

    @Override
    public Pair<Constraint, InfProofStepInfo> applyToImplication(final Implication implication, final Abortion aborter)
        throws AbortionException
    {
        final D data = this.prepare(implication, aborter);
        final Pair<ConstraintSet, Boolean> condResult =
            this.processConstraintSet(implication, implication.getConditions(), false, data, aborter);
        boolean changed = condResult.y;
        final ConstraintSet newCondition = condResult.x;
        Constraint newConclusion;
        if (changed && this.mode == Mode.SingleStep) {
            newConclusion = implication.getConclusion();
        } else {
            if (implication.getConclusion().isConstraintSet()) {
                final Pair<ConstraintSet, Boolean> conclResult =
                    this.processConstraintSet(implication, (ConstraintSet) implication.getConclusion(), true, data, aborter);
                newConclusion = conclResult.x;
                changed = changed || conclResult.y;
            } else {
                newConclusion = this.processConstraint(implication, implication.getConclusion(), true, data, aborter);
                changed = changed || newConclusion != implication.getConclusion();
            }
        }
        if (changed) {
            final Constraint res =
                Implication.create(
                    implication.getId(),
                    implication.getQuantor(),
                    newCondition,
                    newConclusion,
                    implication.getData());
            return new Pair<>(res, InfProofStepInfo.INF_DUMMY_PROOF);
        } else {
            return null;
        }
    }

    protected abstract D prepare(Implication implication, Abortion aborter);

    /**
     *
     * @param constraints
     * @param data
     * @param aborter TODO
     * @return new onstraints, changed
     */
    protected Pair<ConstraintSet, Boolean> processConstraintSet(
        final Implication origImplication,
        final ConstraintSet constraints,
        final boolean isConclusion,
        final D data,
        final Abortion aborter) throws AbortionException
    {
        LinkedHashSet<Constraint> newConstraints = null;
        boolean changed = false;
        for (final Constraint constraint : constraints) {
            final Constraint newConstraint =
                this.processConstraint(origImplication, constraint, isConclusion, data, aborter);
            if (newConstraint != constraint) {
                if (newConstraints == null) {
                    newConstraints = new LinkedHashSet<Constraint>(constraints);
                }
                newConstraints.remove(constraint);
                if (newConstraint != null) {
                    newConstraints.add(newConstraint);
                }
                changed = true;
                if (this.mode == Mode.SingleStep) {
                    break;
                }
            }
        }
        return changed
            ? new Pair<ConstraintSet, Boolean>(ConstraintSet.create(newConstraints), changed)
                : new Pair<ConstraintSet, Boolean>(constraints, false);
    }

    /**
     * @param constraint The constraint to be processed
     * @param data
     * @param aborter TODO
     * @return constraint given if no changes are made (same object!) or a new constraint or
     * <code>null</code> if constraint should be deleted
     * @throws AbortionException TODO
     */
    protected abstract Constraint processConstraint(
        Implication origImplication,
        Constraint constraint,
        boolean isConclusion,
        D data,
        Abortion aborter) throws AbortionException;

}
