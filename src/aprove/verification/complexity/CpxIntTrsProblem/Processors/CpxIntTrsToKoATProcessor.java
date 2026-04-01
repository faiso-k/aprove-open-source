package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;

import aprove.strategies.Annotations.*;

public class CpxIntTrsToKoATProcessor extends CpxIntTrsToKoATLikeBackendProcessor<CpxIntTrsToKoATProcessor.Arguments> {

    public static class Arguments extends CpxIntTrsToKoATLikeBackendProcessor.Arguments {
        public String smtSolver = "z3-internal";
        public int timeout = 0; //in s
    }

    @ParamsViaArgumentObject
    public CpxIntTrsToKoATProcessor(Arguments args) {
        super(args);
    }

    @Override
    public String getToolName() {
        return "koat";
    }

    @Override
    public AnalysisGoal getAnalysisGoal() {
        return AnalysisGoal.UpperBound;
    }

    @Override
    public List<String> getCommandLineArgs() {
        List<String> parameters = new ArrayList<>(4);
        parameters.add("-smt-solver");
        parameters.add(args.smtSolver);
        if (this.args.timeout > 0) {
            parameters.add("-timeout");
            parameters.add(String.valueOf(this.args.timeout));
        }
        return parameters;
    }
}