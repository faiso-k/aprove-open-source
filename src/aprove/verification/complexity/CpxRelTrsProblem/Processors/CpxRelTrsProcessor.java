package aprove.verification.complexity.CpxRelTrsProblem.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;

public abstract class CpxRelTrsProcessor extends ProcessorSkeleton {

    @Override
    public Result process(final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {
        if (!(obl instanceof CpxRelTrsProblem)) {
            return ResultFactory.notApplicable();
        }
        return this.processCpxRelTrs((CpxRelTrsProblem) obl, aborter, rti);
    }

    abstract protected Result processCpxRelTrs(CpxRelTrsProblem obl, Abortion aborter, RuntimeInformation rti);

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (!(obl instanceof CpxRelTrsProblem)) {
            return false;
        }
        return this.isCpxRelTrsApplicable((CpxRelTrsProblem) obl);
    }

    abstract protected boolean isCpxRelTrsApplicable(CpxRelTrsProblem obl);
}
