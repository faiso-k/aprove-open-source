/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.utility.*;

public interface IInitialItpfRule extends ISoundItpfRule {

    /**
     * Used for initial creation of integer pair graph.
     * @param formula - the formula
     * @param aborter - the aborter, that should be checked many times against timeouts/aborts, ...
     * @return The result of this processor
     * @throws AbortionException
     */
    public Itpf processInitial(IDPRuleAnalysis ruleAnalysis, Itpf formula, Abortion aborter) throws AbortionException;

}
