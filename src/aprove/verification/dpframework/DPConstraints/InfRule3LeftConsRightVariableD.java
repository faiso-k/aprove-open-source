package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 * This InfRule removes a ReducesTo of the form t = x were t contains only constructors and x is a Variable
 * and x occures no where on a left-hand side of a ReducesTo
 * and thereby the substitution [x/t] is applied to the new implication
 *
 * @author swiste
 */
public class InfRule3LeftConsRightVariableD extends InfRuleReducesToReplace {

    @Override
    public InfRuleID getID() {
        return InfRuleID.III;
    }

    @Override
    public Mode actionForReducesTo(final ReducesTo reducesTo, final Implication implication, final Abortion aborter) {
        if (reducesTo.getRight().isVariable()) {
            if (this.checkLeftOccur((TRSVariable) reducesTo.getRight(), implication)) {
                return Mode.NoChange;
            }
            if (this.irc.isGround(reducesTo.getLeft())) {
                return Mode.Expand;
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
        return TRSSubstitution.create((TRSVariable) reducesTo.getRight(), reducesTo.getLeft());
    }

    @Override
    public String getLongName() {
        return "Rule IIID: Variable on Right-Hand side";
    }

    @Override
    public String getName() {
        // TODO Auto-generated method stub
        return "Rule IIID";
    }

}
