package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;

/*
 * This InfRule removes als ReducesTo
 */
public class InfRule4DeleteC extends InfRuleReducesToReplace {

    @Override
    public InfRuleID getID() {
        return InfRuleID.IV;
    }

    @Override
    public String getLongName() {
        return "Rule IVC: Delete Conditions (all equations)";
    }

    @Override
    public String getName() {
        return "Rule IVC";
    }

    @Override
    public Mode actionForReducesTo(final ReducesTo reducesTo, final Implication implication, final Abortion aborter) {
        this.irc.setMark(reducesTo);
        return Mode.Delete;
    }

    @Override
    public TRSSubstitution expandReducesTo(
        final ReducesTo reducesTo,
        final Set<Constraint> ncs,
        final Map<Integer, TRSVariable> newVars,
        final Implication implication,
        final Abortion aborter) throws AbortionException
    {
        return null; // Expand to nothing => reducesTo is deleted;
    }

}
