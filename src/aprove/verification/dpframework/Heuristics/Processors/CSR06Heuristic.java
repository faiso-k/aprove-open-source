package aprove.verification.dpframework.Heuristics.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;

@NoParams
public class CSR06Heuristic extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        boolean innermost = ((CSRProblem) obl).getInnermost();
        return ResultFactory.justANewStrategy(new VariableStrategy(innermost ? "csrInn" : "csrTerm").getExecutableStrategy(oblNode, rti));
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof CSRProblem;
    }

}
