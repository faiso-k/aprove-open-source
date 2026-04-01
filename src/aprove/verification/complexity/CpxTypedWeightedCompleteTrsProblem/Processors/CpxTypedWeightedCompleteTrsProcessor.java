package aprove.verification.complexity.CpxTypedWeightedCompleteTrsProblem.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxTypedWeightedCompleteTrsProblem.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;

public abstract class CpxTypedWeightedCompleteTrsProcessor extends ProcessorSkeleton {

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (obl instanceof CpxTypedWeightedCompleteTrsProblem) {
            return isCpxTypedWeightedCompleteTrsApplicable((CpxTypedWeightedCompleteTrsProblem)obl);
        }
        return false;
    }

    @Override
    public Result process(final BasicObligation obl, final BasicObligationNode oblNode,
            final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final CpxTypedWeightedCompleteTrsProblem trs = (CpxTypedWeightedCompleteTrsProblem)obl;
        return processCpxTypedWeightedCompleteTrs(trs, aborter);
    }

    protected abstract boolean isCpxTypedWeightedCompleteTrsApplicable(CpxTypedWeightedCompleteTrsProblem obl);

    protected abstract Result processCpxTypedWeightedCompleteTrs(CpxTypedWeightedCompleteTrsProblem cpxTrs,
            Abortion aborter) throws AbortionException;

}
