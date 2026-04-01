package aprove.verification.dpframework.Heuristics.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;

public class MRR06Heuristic extends Processor.ProcessorSkeleton {

    private final String sub1;
    private final String sub2;

    private final boolean allowATrans;

    @ParamsViaArgumentObject
    public MRR06Heuristic(Arguments arguments) {
        this.allowATrans = arguments.allowATransformation;
        this.sub1 = arguments.sub1;
        this.sub2 = arguments.sub2;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        QDPProblem qdp = (QDPProblem) obl;
        boolean usableRulesRP = UsableRulesReductionPairsProcessor.checkApplication(qdp, this.allowATrans);
        return ResultFactory.justANewStrategy(new VariableStrategy(usableRulesRP ? this.sub1 : this.sub2).getExecutableStrategy(oblNode, rti));
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof QDPProblem;
    }

    public static class Arguments {
        public boolean allowATransformation = true;
        public String sub1;
        public String sub2;
    }
}
