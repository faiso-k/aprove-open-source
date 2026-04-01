package aprove.verification.oldframework.WeightedIntTrs;

import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.*;

public class WeightedIntTrsToLoATProcessor extends WeightedIntTrsToKoATLikeBackendProcessor<CpxIntTrsToLoATProcessor.Arguments, CpxIntTrsToLoATProcessor> {

    @ParamsViaArgumentObject
    public WeightedIntTrsToLoATProcessor(CpxIntTrsToLoATProcessor.Arguments args) {
        super(new CpxIntTrsToLoATProcessor(args));
    }

}
