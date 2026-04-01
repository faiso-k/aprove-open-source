package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;

/*
 * this InfRule remove a ReducesTo of the form x = q if x is a variable
 * if q is a no normalform the whole implication is erased
 * if q is a normalform the substitution [x/q] is applied to the resulting implication without the ReducesTo x = q
 */
public class InfRule3LeftVariableC extends InfRuleReducesToReplace {

    @Override
    public InfRuleID getID() {
        return InfRuleID.III;
    }

    @Override
    public String getLongName() {
        return "Rule IIIC: Variable on Left-Hand Side (full)";
    }

    @Override
    public String getName() {
        return "Rule IIIC";
    }

    @Override
    public Mode actionForReducesTo(final ReducesTo reducesTo, final Implication implication, final Abortion aborter) {
        if (reducesTo.notBlocked(this)) {
            if (reducesTo.getLeft().isVariable()) {
                this.irc.setMark(reducesTo);
                return (this.irc.isNormal(reducesTo.getRight())) ? Mode.Expand : Mode.Erase;
            }
            reducesTo.block(this);
        }
        return Mode.NoChange;
    }

    @Override
    public TRSSubstitution expandReducesTo(
        final ReducesTo reducesTo,
        final Set<Constraint> ncs,
        final Map<Integer, TRSVariable> newVars,
        final Implication implication,
        final Abortion aborter) throws AbortionException
    {
        return TRSSubstitution.create((TRSVariable) reducesTo.getLeft(), reducesTo.getRight());
    }

}
