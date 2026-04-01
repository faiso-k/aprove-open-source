package aprove.verification.dpframework.DPConstraints;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.idp.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;

/**
 * This InfRule removes a ReducesTo of the form t = x were t contains only constructors and x is a Variable
 * and thereby the substitution [x/t] is applied to the new implication
 *
 * @author swiste
 */
public class InfRule3LeftConsRightVariableE extends InfRule3LeftConsRightVariableD {

    @Override
    public InfRuleID getID() {
        return InfRuleID.III;
    }

    @Override
    public String getLongName() {
        return "Rule IIIE: Variable on Right-Hand side (full)";
    }

    @Override
    public String getName() {
        // TODO Auto-generated method stub
        return "Rule IIIE";
    }

    @Override
    public Mode actionForReducesTo(ReducesTo reducesTo, Implication implication, Abortion aborter) {
        if (reducesTo.getRight().isVariable()) {
            if (this.checkLeftOccur((TRSVariable) reducesTo.getRight(), implication)) {
                return Mode.NoChange;
            }
            if (this.irc.isGround(reducesTo.getLeft())
                || (this.irc.isIdpMode() && PredefinedUtil.onlyPredefined(reducesTo.getLeft(), ((IdpInductionCalculus) this.irc)
                    .getIdp()
                    .getRuleAnalysis()
                    .getPreDefinedMap())))
            {
                return Mode.Expand;
            }
        }
        return Mode.NoChange;

    }

    @Override
    public boolean checkLeftOccur(TRSVariable x, Implication implication) {
        return false;
    }

}
