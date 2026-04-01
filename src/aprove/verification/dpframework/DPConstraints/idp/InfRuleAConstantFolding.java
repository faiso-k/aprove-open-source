/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.utility.*;

public class InfRuleAConstantFolding extends InfRuleConstraintRepl<Object> {

    public InfRuleAConstantFolding() {
        super(Mode.Full);
    }

    @Override
    public InfRuleID getID() {
        return InfRuleID.IDP_CONSTANT_FOLD;
    }

    @Override
    public String getLongName() {
        return "Rule IDP_A: constant folding ReducesTo lhs if rhs NF";
    }

    @Override
    public String getName() {
        return "Rule A";
    }

    @Override
    protected Constraint processConstraint(
        Implication origImplication,
        Constraint constraint,
        boolean isConclusion,
        Object data,
        Abortion aborter) throws AbortionException
    {
        if (constraint.isReducesTo()) {
            ReducesTo r = (ReducesTo) constraint;
            if (this.getIrc().isNormal(r.getRight())) {
                IDPPredefinedMap predefinedMap =
                    ((IdpInductionCalculus) this.irc).getIdp().getRuleAnalysis().getPreDefinedMap();
                TRSTerm newLeft = ConstantFolding.fold(r.getLeft(), predefinedMap);
                if (!r.getLeft().equals(newLeft)) {
                    // System.err.println("FOLD: " + r.getLeft() + " TO " + newLeft);
                    return ReducesTo.create(newLeft, r.getRight(), null, r.getCount(), r.getId());
                }
            }
        }
        // nothing to do
        return constraint;
    }

    @Override
    protected Object prepare(Implication implication, Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

}
