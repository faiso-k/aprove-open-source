package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * ConstNarr07Condition.<br><br>
 *
 * Created: May 8, 2007<br>
 * Last modified: May 8, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public class BranchingCondition extends AbstractQDPCondition {

    @Override
    public boolean checkQDP(QDPProblem qdp, Abortion aborter) {
        Graph<Rule, ? > g = qdp.getDependencyGraph().getGraph();
        for (Node<Rule> n : g.getNodes()) {
            if (g.getOut(n).size() > 1) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return true;
    }

}
