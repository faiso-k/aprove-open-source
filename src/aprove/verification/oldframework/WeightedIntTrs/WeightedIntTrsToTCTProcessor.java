package aprove.verification.oldframework.WeightedIntTrs;

import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.CpxIntTrsToKoATProcessor.*;

public class WeightedIntTrsToTCTProcessor extends WeightedIntTrsToKoATLikeBackendProcessor<CpxIntTrsToTCTProcessor.Arguments, CpxIntTrsToTCTProcessor> {

    @ParamsViaArgumentObject
    public WeightedIntTrsToTCTProcessor(Arguments args) {
        super(new CpxIntTrsToTCTProcessor(args));
    }

}
