package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Heuristics.*;

/**
 * AbstractQDPCondition.<br><br>
 *
 * Created: May 8, 2007<br>
 * Last modified: May 8, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public abstract class AbstractQDPCondition implements Condition {

    @Override
    public boolean check(BasicObligation obl, Abortion aborter, RuntimeInformation rti) {
        return this.checkQDP((QDPProblem) obl, aborter);
    }
    public abstract boolean checkQDP(QDPProblem qdp, Abortion aborter);

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof QDPProblem) && this.isQDPApplicable((QDPProblem) obl);
    }
    public abstract boolean isQDPApplicable(QDPProblem qdp);
}
