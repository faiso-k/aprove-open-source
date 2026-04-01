/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;

public class InfRuleDeleteTrivialReducesTo extends InfRuleReducesToReplace {

    @Override
    public Mode actionForReducesTo(final ReducesTo reducesTo, final Implication implication, final Abortion aborter) {
        if (reducesTo.getLeft().equals(reducesTo.getRight())) {
            return Mode.Expand;
        } else {
            return Mode.NoChange;
        }
    }

    @Override
    public TRSSubstitution expandReducesTo(
        final ReducesTo reducesTo,
        final Set<Constraint> ncs,
        final Map<Integer, TRSVariable> newVars,
        final Implication implication,
        final Abortion aborter) throws AbortionException
    {
        return null;
    }

    @Override
    public InfRuleID getID() {
        return InfRuleID.DELETE_TRIVIAL_REDUCESTO;
    }

    @Override
    public String getLongName() {
        return "Rule DeleteTrivialReducesTo: erase t = t";
    }

    @Override
    public String getName() {
        return "Rule DeleteTrivialReducesTo";
    }

}
