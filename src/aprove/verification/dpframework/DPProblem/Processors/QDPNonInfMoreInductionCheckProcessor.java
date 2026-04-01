package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.DPConstraints.Implication;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.theoremprover.TerminationProofs.*;

@NoParams
public class QDPNonInfMoreInductionCheckProcessor extends QDPProblemProcessor {

    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter)
            throws AbortionException {
        // TODO Auto-generated method stub
        ConstraintsCache<Rule> cc = qdp.getConstraintsCache();

        if (!cc.isEmpty()) {
            int i=0;
            for (Map.Entry<Rule,List<Implication>> entry : cc.getProblemMap().entrySet()){
                for (Implication imp : entry.getValue()){
                    //System.out.println(imp);
                    i++;
                    if (!imp.getConditions().isEmpty()) {
                        return ResultFactory.unsuccessful();
                    }
                }

            }
            if (i>2) {
                return ResultFactory.unsuccessful();
            }
            return ResultFactory.proved(qdp.getSameProblemAndFillCache(cc), YNMImplication.EQUIVALENT,new NeedMoreInductionProof());
        }
        return ResultFactory.unsuccessful();
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return qdp.getInnermost() && qdp.getMinimal();
    }

    private static final class NeedMoreInductionProof extends Proof {

        @Override
        public String export(Export_Util o) {
            return o.export("DP Constraints are not suitable.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
