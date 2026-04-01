package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;

/*
 * This InfRule delete ReducesTo of form q = x where x is a variable and x does not occur anywhere else.
 */
public class InfRule4DeleteA extends InfRuleReducesToReplace {

    @Override
    public InfRuleID getID() {
        return InfRuleID.IV;
    }

    @Override
    public String getLongName() {
        return "Rule IVA: Delete Conditions (q = x, with lonely Variable x)";
    }

    @Override
    public String getName() {
        return "Rule IVA";
    }

    @Override
    public Mode actionForReducesTo(final ReducesTo reducesTo, final Implication implication, final Abortion aborter) {
        if (reducesTo.getRight().isVariable()) {
            if (this.irc.occursOnce((TRSVariable) reducesTo.getRight())) {
                //System.out.println("::::::::::::"+(Variable)reducesTo.getRight());
                this.irc.setMark(reducesTo);
                return Mode.Delete;
            }

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
        return null; // no Substitution and empty replacement
    }
}
