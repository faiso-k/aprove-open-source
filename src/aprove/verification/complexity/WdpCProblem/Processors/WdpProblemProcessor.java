package aprove.verification.complexity.WdpCProblem.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.WdpCProblem.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;

public abstract class WdpProblemProcessor extends ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof WDPProblemRC) {
            return this.isWdpApplicable((WDPProblemRC) obl);
        }
        return false;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {
        WDPProblemRC wdpProblem = (WDPProblemRC)obl;
        return this.processWdp(wdpProblem, aborter);
    }

    protected abstract boolean isWdpApplicable(WDPProblemRC obl);

    protected abstract Result processWdp(WDPProblemRC wdpProblem,
            Abortion aborter) throws AbortionException;

}
