package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This InfRule removes all inner implications
 * @author swiste
 *
 */
public class InfRule4DeleteD extends InfRule {

    @Override
    public InfRuleID getID() {
        return InfRuleID.IV;
    }

    @Override
    public String getLongName() {
        return "Rule IVD: Delete Conditions (remove all inner implications)";
    }

    @Override
    public String getName() {
        return "Rule IVD";
    }

    @Override
    public Pair<Constraint, InfProofStepInfo> applyToImplication(final Implication implication, final Abortion aborter)
        throws AbortionException
    {
        final List<Constraint> cs = new LinkedList<>();
        boolean change = false;
        for (final Constraint con : implication.getConditions()) {
            if (!con.isImplication()) {
                cs.add(con);
            } else {
                this.irc.setMark(null);
                change = true;
            }
        }
        if (!change) {
            return null;
        }
        final Implication res =
            Implication.create(
                implication.getQuantor(),
                ConstraintSet.flatCreate(cs),
                implication.getConclusion(),
                implication.getData());
        return new Pair<Constraint, InfProofStepInfo>(res, new InfRule4DeleteProof(res));
    }

}
