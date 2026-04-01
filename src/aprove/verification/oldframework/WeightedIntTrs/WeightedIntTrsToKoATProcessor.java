package aprove.verification.oldframework.WeightedIntTrs;

import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.CpxIntTrsToKoATProcessor.*;

public class WeightedIntTrsToKoATProcessor extends WeightedIntTrsToKoATLikeBackendProcessor<CpxIntTrsToKoATProcessor.Arguments, CpxIntTrsToKoATProcessor> {

    public WeightedIntTrsToKoATProcessor() {
        this(new CpxIntTrsToKoATProcessor.Arguments());
    }

    @ParamsViaArgumentObject
    public WeightedIntTrsToKoATProcessor(Arguments args) {
        super(new CpxIntTrsToKoATProcessor(args));
    }

}
