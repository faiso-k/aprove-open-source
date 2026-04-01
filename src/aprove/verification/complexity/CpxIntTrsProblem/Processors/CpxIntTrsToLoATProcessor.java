package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;
import java.util.regex.*;

import aprove.strategies.Annotations.*;

/**
 * Ask LoAT for a lower runtime complexity bound.
 */
public class CpxIntTrsToLoATProcessor extends CpxIntTrsToKoATLikeBackendProcessor<CpxIntTrsToLoATProcessor.Arguments> {

    public static class Arguments extends CpxIntTrsToKoATLikeBackendProcessor.Arguments {
        public int timeout = Integer.MAX_VALUE;
        public boolean smt = false;
    }

    @ParamsViaArgumentObject
    public CpxIntTrsToLoATProcessor(CpxIntTrsToLoATProcessor.Arguments args) {
        super(args);
    }

    @Override
    public String getToolName() {
        return "loat";
    }

    @Override
    public String obtainResult(List<String> proofText) {
        if (proofText.get(proofText.size() - 1).equals("NO")) {
            return "INF";
        }
        for (String line : proofText) {
            if (line.contains("WORST_CASE")) {
                Pattern p = Pattern.compile("WORST_CASE\\(((?<inf>INF)|(?<exp>EXP)|Omega\\((?<poly>[^,]*)\\)),\\s*[^\\)]*\\)");
                Matcher m = p.matcher(line);
                if (m.find()) {
                    if (m.group("inf") != null) {
                        return "INF";
                    } else if (m.group("exp") != null) {
                        return "EXP";
                    } else {
                        return m.group("poly");
                    }
                }
            }
        }
        return null;
    }

    @Override
    public AnalysisGoal getAnalysisGoal() {
        return AnalysisGoal.LowerBound;
    }

    @Override
    List<String> getCommandLineArgs() {
        List<String> cmdArgs = new ArrayList<>();
        cmdArgs.add("--plain");
        cmdArgs.add("--timeout");
        cmdArgs.add(Integer.toString(args.timeout));
        if (args.smt) {
            cmdArgs.add("--limit-smt");
        }
        return cmdArgs;
    }
}
