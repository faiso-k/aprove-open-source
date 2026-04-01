/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf.rules;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;

public class PCSmt extends IItpfRule.ItpfRuleSkeleton implements IInitialItpfRule, ISoundItpfRule, ICompleteItpfRule {

    @Override
    public Itpf processInitial(IDPRuleAnalysis ruleAnalysis, Itpf formula,
            Abortion aborter) throws AbortionException {
        return null;
    }

    @Override
    public Exportable getDescription(NameLength length) {
        return null;
    }

    @Override
    public boolean isApplicable(IDPProblem idp) {
        return true;
    }

    @Override
    public boolean isApplicable(IDPProblem idp, Itpf fromula,
            ApplicationMode mode) {
        return false;
    }

    @Override
    public Itpf process(IDPProblem idp, Itpf formula, ApplicationMode mode,
            Abortion aborter) throws AbortionException {
        return null;
    }

    protected Itpf processFormula(Itpf formula) {
        return null;
    }

}
