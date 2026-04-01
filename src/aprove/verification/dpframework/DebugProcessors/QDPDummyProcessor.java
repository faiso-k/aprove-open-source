package aprove.verification.dpframework.DebugProcessors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;

public class QDPDummyProcessor extends QDPProblemProcessor  {

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return true;
    }

    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter)
            throws AbortionException {

        Set<Rule> P = new LinkedHashSet<Rule>(qdp.getP());
        QDependencyGraph g = qdp.getDependencyGraph();
        Iterator<Rule> it = P.iterator();
        P.remove(it.next());
        QDependencyGraph g2 = g.getSubGraph(P, qdp.getRwithQ());
        System.err.println("foobar!");


        return ResultFactory.unsuccessful();
    }

}
