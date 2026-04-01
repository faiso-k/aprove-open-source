package aprove.verification.complexity.CpxRelTrsProblem.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;

public abstract class RuntimeComplexityRelTrsProcessor extends ProcessorSkeleton {

    @Override
    public Result process(final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {
        if (!(obl instanceof RuntimeComplexityRelTrsProblem)) {
            return ResultFactory.notApplicable();
        }
        return this.processRuntimeComplexityRelTrs((RuntimeComplexityRelTrsProblem) obl, aborter);
    }

    abstract protected Result processRuntimeComplexityRelTrs(RuntimeComplexityRelTrsProblem obl, Abortion aborter);

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (!(obl instanceof RuntimeComplexityRelTrsProblem)) {
            return false;
        }
        return this.isRuntimeComplexityRelTrsApplicable((RuntimeComplexityRelTrsProblem) obl);
    }

    abstract protected boolean isRuntimeComplexityRelTrsApplicable(RuntimeComplexityRelTrsProblem obl);
}
