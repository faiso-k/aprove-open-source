package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.DPProblem.*;

/**
 * ConstNarr07Condition.<br><br>
 *
 * Created: May 8, 2007<br>
 * Last modified: May 8, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public class SingleRuleCondition extends AbstractQDPCondition {

    @Override
    public boolean checkQDP(QDPProblem qdp, Abortion aborter) {
        return qdp.getP().size() == 1;
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return true;
    }

}
