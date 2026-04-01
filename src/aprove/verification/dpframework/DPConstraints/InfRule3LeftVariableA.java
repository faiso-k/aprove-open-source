package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 *
 * This InfRule checkes the occurence of the ReducesTo of the form x = q where x is a Variable and q is no normalform
 * if it occurs the whole implication is erased.
 *
 * @author swiste
 *
 */
public class InfRule3LeftVariableA extends InfRuleReducesToReplace {

    @Override
    public InfRuleID getID() {
        return InfRuleID.III;
    }

    @Override
    public String getLongName() {
        return "Rule IIIA: Variable on Left-Hand Side (erase no normalform)";
    }

    @Override
    public String getName() {
        return "Rule IIIA";
    }

    @Override
    public Mode actionForReducesTo(final ReducesTo reducesTo, final Implication implication, final Abortion aborter) {
        if (reducesTo.notBlocked(this)) {
            if (reducesTo.getLeft().isVariable()) {
                if (!(this.irc.isNormal(reducesTo.getRight()))) {
                    this.irc.setMark(reducesTo);
                    return Mode.Erase;
                }
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
