package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;

/**
 * MRR06Condition.<br><br>
 *
 * Created: May 8, 2007<br>
 * Last modified: May 8, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public class MRR06Condition extends AbstractQDPCondition {

    private boolean allowATrans = true;

    @Override
    public boolean checkQDP(QDPProblem qdp, Abortion aborter) {
        return UsableRulesReductionPairsProcessor.checkApplication(qdp, this.allowATrans);
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return true;
    }

    public void setAllowATransformation(boolean allow) {
        System.err.println("Kilroy4 was here!");
        this.allowATrans = allow;
    }

}
