package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;

public class CpxIntTrsToTCTProcessor extends CpxIntTrsToKoATLikeBackendProcessor<CpxIntTrsToKoATLikeBackendProcessor.Arguments> {

    public CpxIntTrsToTCTProcessor(Arguments args) {
        super(args);
    }

    @Override
    public String getToolName() {
        return "tct-its";
    }

    @Override
    List<String> getCommandLineArgs() {
        return Collections.emptyList();
    }

    @Override
    public AnalysisGoal getAnalysisGoal() {
        return AnalysisGoal.UpperBound;
    }

}
