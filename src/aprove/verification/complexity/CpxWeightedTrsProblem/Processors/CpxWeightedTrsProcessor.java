package aprove.verification.complexity.CpxWeightedTrsProblem.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;

public abstract class CpxWeightedTrsProcessor extends ProcessorSkeleton {

    @Override
    public Result process(final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {
        if (!(obl instanceof CpxWeightedTrsProblem)) {
            return ResultFactory.notApplicable();
        }
        return this.processCpxWeightedTrs((CpxWeightedTrsProblem) obl, aborter, rti);
    }

    abstract protected Result processCpxWeightedTrs(CpxWeightedTrsProblem obl, Abortion aborter, RuntimeInformation rti);

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (!(obl instanceof CpxWeightedTrsProblem)) {
            return false;
        }
        return this.isCpxWeightedTrsApplicable((CpxWeightedTrsProblem) obl);
    }

    abstract protected boolean isCpxWeightedTrsApplicable(CpxWeightedTrsProblem obl);
}
