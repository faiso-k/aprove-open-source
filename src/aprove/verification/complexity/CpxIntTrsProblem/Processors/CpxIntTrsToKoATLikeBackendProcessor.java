package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.io.*;
import java.util.*;
import java.util.regex.*;

import aprove.api.decisions.impl.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Algorithms.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;

public abstract class CpxIntTrsToKoATLikeBackendProcessor<T extends CpxIntTrsToKoATLikeBackendProcessor.Arguments> extends CpxIntTrsProcessor {

    public static enum AnalysisGoal {
        LowerBound, UpperBound
    }

    public static class Arguments {
        public String filename = null;
    }

    private TransitionProgram tp;

    T args;

    @ParamsViaArgumentObject
    public CpxIntTrsToKoATLikeBackendProcessor(T args) {
        this.args = args;
    }
    
    public ComplexityValue readFromKoatLikeParser(String resultText) {
        return KoATParser.parse(resultText);
    }

    @Override
    public Result processCpxIntTrs(CpxIntTrsProblem obl,
            BasicObligationNode oblNode,
            Abortion aborter,
            RuntimeInformation rti) throws AbortionException {
        aborter.checkAbortion();
        String exportString = this.obtainExport(obl, aborter);
        aborter.checkAbortion();
        List<String> proofText = this.obtainProof(exportString, aborter);
        if (proofText == null) {
            System.err.println("External unsuccessful!");
            return ResultFactory.unsuccessful();
        }
        String resultText = this.obtainResult(proofText);
        if (resultText == null) {
            return ResultFactory.unsuccessful();
        }
        ComplexityValue compl = this.readFromKoatLikeParser(resultText);
        if (compl == null) {
            return ResultFactory.unsuccessful();
        }
        return buildResult(compl, proofText);
    }

    public Result buildResult(ComplexityValue compl, List<String> proofText) {
        switch (getAnalysisGoal()) {
            case LowerBound: return ResultFactory.provedWithValue(ComplexityYNM.createLower(compl),
                    new KoATLikeProof(getToolName(), proofText));
            case UpperBound: return ResultFactory.provedWithValue(ComplexityYNM.createUpper(compl),
                    new KoATLikeProof(getToolName(), proofText));
            default: throw new RuntimeException("Unknown Analysis Goal");
        }
    }

    @Override
    boolean isCpxIntTrsApplicable(CpxIntTrsProblem obl) {
        return isInstalled();
    }

    public boolean isInstalled() {
        return LocalToolDetector.cintBackendExists(getToolName());
    }

    public abstract AnalysisGoal getAnalysisGoal();
    public abstract String getToolName();
    abstract List<String> getCommandLineArgs();

    public String obtainExport(CpxIntTrsProblem obl, Abortion aborter) {
        tp = CpxIntTrsNormalizer.toTransitionProgram(obl, aborter);
        tp = tp.normalizeVars();
        StringBuilder sb = new StringBuilder();
        tp.toKOAT(sb);
        return sb.toString();
    }

    public List<String> obtainProof(String export, Abortion aborter) {
        Process process = null;
        try {
            // create input file
            File input;
            if (this.args.filename == null) {
                input = File.createTempFile("aprove", ".koat");
                input.deleteOnExit();
            } else {
                input = new File(this.args.filename);
            }
            // write ITS to input file
            Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(export);
            inputWriter.close();
            // construct the invocation
            List<String> parameters = new ArrayList<String>();
            parameters.add(getToolName());
            parameters.addAll(getCommandLineArgs());
            parameters.add(input.getCanonicalPath());
            // start the process
            ProcessBuilder processBuilder = new ProcessBuilder(parameters.toArray(new String[parameters.size()]));
            processBuilder.redirectErrorStream(true);
            process = processBuilder.start();
            TrackerFactory.process(aborter, process);
            // read the output
            List<String> proofText = new LinkedList<>();
            try (BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()))) {
                for (String line = reader.readLine(); line != null; line = reader.readLine()) {
                    proofText.add(line);
                }
            }
            // done
            process.waitFor();
            return proofText;
        } catch (IOException ex) {
            ex.printStackTrace();
            return null;
        } catch (InterruptedException ex) {
            safelyDestroy(process);
            return null;
        } catch (ThreadDeath td) {
            safelyDestroy(process);
            throw td;
        } finally {
            // the special cases for InterruptedEx and ThreadDeath are necessary
            // as the finally block is not guaranteed to be executed in these cases
            safelyDestroy(process);
        }
    }

    private void safelyDestroy(Process proc) {
        if (proc != null && proc.isAlive()) {
            proc.destroyForcibly();
        }
    }

    public String obtainResult(List<String> proofText) {
        for (String line : proofText) {
            if (line.contains("YES")) {
                Pattern p = Pattern.compile("YES\\(.*?, ?(.*)\\)");
                Matcher m = p.matcher(line);
                if (m.find()) {
                    return m.group(1);
                }
            }
        }
        return null;
    }

    public static class KoATLikeProof extends Proof.DefaultProof {

        private final String tool;
        private final List<String> proofText;

        public String getTool() {
            return tool;
        }

        public KoATLikeProof(String tool, final List<String> proofText) {
            this.tool = tool.substring(0, 1).toUpperCase() + tool.substring(1);
            this.setShortName(this.tool + " Proof");
            this.setLongName(this.tool + " Proof");
            this.proofText = proofText;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();
            for (final String s : this.proofText) {
                result.append(s);
                result.append(o.newline());
            }
            return result.toString();
        }
    }
}
