package aprove.verification.complexity.CdpProblem.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdpProblem.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;

public abstract class CdpProblemProcessor extends ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof CdpProblem) {
            return this.isCdpApplicable((CdpProblem) obl);
        }
        return false;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {
        CdpProblem cdpProblem = (CdpProblem)obl;
        return this.processCdp(cdpProblem, aborter);
    }

    protected abstract boolean isCdpApplicable(CdpProblem obl);

    protected abstract Result processCdp(CdpProblem CdpProblem,
            Abortion aborter) throws AbortionException;

}
