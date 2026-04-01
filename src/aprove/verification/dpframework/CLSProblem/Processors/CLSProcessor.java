package aprove.verification.dpframework.CLSProblem.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.CLSProblem.*;

public abstract class CLSProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {
        CLSProblem problem = (CLSProblem) obl;
        return this.processCLS(problem, aborter);
    }

    protected abstract Result processCLS(CLSProblem problem, Abortion aborter) throws AbortionException;

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof CLSProblem) {
            return this.isCLSApplicable((CLSProblem) obl);
        }
        return false;
    }

    public abstract boolean isCLSApplicable(CLSProblem obl);
}
