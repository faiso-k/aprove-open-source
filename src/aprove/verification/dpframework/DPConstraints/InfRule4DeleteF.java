package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;

/*
 * This InfRule delete ReducesTo q = x, where x occur only once and q is big constructor term
 */
public class InfRule4DeleteF extends InfRuleReducesToReplace {

    @Override
    public InfRuleID getID() {
        return InfRuleID.IV;
    }

    @Override
    public String getLongName() {
        return "Rule IVF: Delete Conditions (q = x, where x occur only once and q is big constructor term)";
    }

    @Override
    public String getName() {
        return "Rule IVF";
    }

    @Override
    public Mode actionForReducesTo(final ReducesTo reducesTo, final Implication implication, final Abortion aborter) {
        if (reducesTo.getRight().isVariable()) {
            if (this.irc.occursNTimes((TRSVariable) reducesTo.getRight(), 2)) {
                final TRSTerm t = reducesTo.getLeft();
                if (this.irc.isGround(t) && (t.getDepth() > 2)) {
                    if (Globals.DEBUG_SWISTE || Globals.DEBUG_MPLUECKER) {
                        System.out.println("::::::::::::" + reducesTo.getRight());
                    }
                    this.irc.setMark(reducesTo);
                    return Mode.Delete;
                }
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
