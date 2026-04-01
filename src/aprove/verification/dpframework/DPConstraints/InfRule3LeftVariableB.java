package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;

/*
 * This InfRule removes the ReducesTo of the form x = q if x is a variable and
 * q is a variable or x occurs no where in a left-hand side of a ReducesTo as argument of a defined symbol
 * if q is a no normalform the whole implication is erased
 * if q is a normalform the substitution [x/q] is applied to the resulting implication without the ReducesTo x = q
 */
public class InfRule3LeftVariableB extends InfRuleReducesToReplace {

    @Override
    public InfRuleID getID() {
        return InfRuleID.III;
    }

    @Override
    public String getLongName() {
        return "Rule IIIB: Variable on Left-Hand Side (does not occur in an argument)";
    }

    @Override
    public String getName() {
        return "Rule IIIB";
    }

    @Override
    public Mode actionForReducesTo(final ReducesTo reducesTo, final Implication implication, final Abortion aborter) {
        if (reducesTo.getLeft().isVariable()) {
            if (reducesTo.getRight().isVariable() && this.checkLeftOccur((TRSVariable) reducesTo.getLeft(), implication)) {
                return Mode.NoChange;
            }
            this.irc.setMark(reducesTo);
            // System.out.println("actionForReducesTo " + implication);
            return (this.irc.isNormal(reducesTo.getRight())) ? Mode.Expand : Mode.Erase;
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
