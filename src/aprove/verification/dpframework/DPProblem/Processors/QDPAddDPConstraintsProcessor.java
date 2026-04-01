package aprove.verification.dpframework.DPProblem.Processors;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.DPConstraints.AbstractInductionCalculus.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Logic.*;

public class QDPAddDPConstraintsProcessor extends QDPProblemProcessor {
    private final int leftChainCounter;
    private final int rightChainCounter;
    private final int inductionCounter;
    private final int minImplications;

    @ParamsViaArgumentObject
    public QDPAddDPConstraintsProcessor(Arguments arguments) {
        this.leftChainCounter = arguments.leftChainCounter;
        this.rightChainCounter = arguments.rightChainCounter;
        this.inductionCounter = arguments.inductionCounter;
        this.minImplications = arguments.minImplications;
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return qdp.getInnermost() && qdp.getMinimal();
    }

    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter)
    throws AbortionException {
        Options options =
            new Options(this.leftChainCounter, this.rightChainCounter, this.inductionCounter, 0);
        ConstraintsCache<Rule> constraintsCache = qdp.getConstraintsCache();
        InductionCalculusProof icProof;
        if (constraintsCache.needsRefresh(options)) {
            icProof = new InductionCalculusProof(qdp,options);
            InductionCalculus ic =
                new InductionCalculus(qdp, icProof, options, aborter);
            constraintsCache = ic.generateConstraintsCache();
        } else {
            icProof = constraintsCache.getProofForP(qdp);
        }
        if (this.minImplications == 0 || constraintsCache.countRealImplications() >= this.minImplications) {
            return ResultFactory.proved(qdp.getSameProblemAndFillCache(constraintsCache),YNMImplication.EQUIVALENT,icProof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    public static class Arguments {
        public int leftChainCounter;
        public int rightChainCounter;
        public int inductionCounter;
        public int minImplications;
    }

}
