package aprove.verification.dpframework.ExternalTpdbTool;

import java.io.*;
import java.util.*;

import javax.xml.parsers.*;
import javax.xml.transform.*;

import aprove.cli.tpdbConverter.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Result;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Start an external process with TPDB/TermComp calling conventions.
 */
public class ExternalTpdbToolProcessor extends Processor.ProcessorSkeleton {

    /**
     * Arguments for the Processor.
     */
    public static class Arguments {
        /** Executable of tool, to be started with:
         * <code>executable PROBLEMFILE TIMEOUT</code>
         */
        public String executable = "";
        /**
         * Determines whether to look for Termination or Complexity results in the output of the tool.
         */
        public GoalType goal = GoalType.TERMINATION;
        /**
         * Number of seconds passed to the external Tool.
         */
        public int timeout = 60;
    }

    /**
     * What type of proposition the external tool shows.
     */
    public enum GoalType {
        /** External Processor gives an upper bound of complexity */
        COMPLEXITY,
        /** External Processor gives a termination result (i.e., YES/NO/MAYBE) */
        TERMINATION
    }

    /**
     * The Arguments used by the Processor.
     */
    private final Arguments args;

    /**
     * The one and only constructor.
     * @param _args the arguments.
     */
    @ParamsViaArgumentObject
    public ExternalTpdbToolProcessor(final Arguments _args) {
        this.args = _args;
    }

    /**
     * Copies the input stream into a StringBuilder. If this provides useful, move it to a more visible place.
     * @param input The Reader to read.
     * @param output The stream will be appended to this StringBuilder.
     * @throws IOException If the Reader is unhappy.
     */
    private static void readAll(final Reader input, final StringBuilder output) throws IOException {
        final char[] cbuf = new char[4096];
        int len;
        while ((len = input.read(cbuf)) != -1) {
            output.append(cbuf, 0, len);
        }
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return TPDB_Exporter.isExportable(obl);
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        Process process = null;
        String resultLine;
        final StringBuilder proofOutput = new StringBuilder();
        File file = null;
        try {
            file = TPDB_Exporter.toTemporaryXMLFile(obl);
            // delete this file afterwards...
            TPDB_Exporter.toXMLString(obl, file.getAbsolutePath());
            final ArrayList<String> parameters = new ArrayList<>();
            parameters.add(this.args.executable);
            parameters.add(file.getAbsolutePath());
            parameters.add(Integer.toString(this.args.timeout));
            final ProcessBuilder processBuilder = new ProcessBuilder(parameters.toArray(new String[] {}));
            process = processBuilder.start();
            TrackerFactory.process(aborter, process);
            // we do not need to send anything to the process, so don't make it wait
            process.getOutputStream().close();
            // what to do about stderr of the process?
            final BufferedReader stdOut = new BufferedReader(new InputStreamReader(process.getInputStream()));
            resultLine = stdOut.readLine();
            ExternalTpdbToolProcessor.readAll(stdOut, proofOutput);
        } catch (TransformerException | ParserConfigurationException | IOException e) {
            return ResultFactory.error(e);
        } finally {
            if (process != null) {
                process.destroy(); // clean up
            }
            if (file != null) {
                file.delete();
            }
        }

        final Proof proof = new Proof.DefaultProof() {
            @Override
            public String export(final Export_Util o, final VerbosityLevel level) {
                return o.preFormatted(o.escape(proofOutput.toString()));
            }
        };

        switch (this.args.goal) {
        case COMPLEXITY:
            try {
                final Pair<ComplexityValue, ComplexityValue> lowerUpper = ComplexityResultParser.parse(resultLine);
                return ResultFactory.provedWithValue(ComplexityYNM.create(lowerUpper.x, lowerUpper.y), proof);
            } catch (final ComplexityResultParser.ParserException e) {
                // fall through to unsuccessful result
            }
            break;
        case TERMINATION:
            switch (resultLine.trim()) {
            case "YES":
                return ResultFactory.proved(proof);
            case "NO":
                return ResultFactory.disproved(proof);
            }
        }
        return ResultFactory.unsuccessful("Strange result from external processor: \"" + resultLine + "\"");
    }
}
