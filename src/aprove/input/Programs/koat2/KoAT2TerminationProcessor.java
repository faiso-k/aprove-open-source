package aprove.input.Programs.koat2;

import java.io.*;
import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.processors.*;
import aprove.input.Programs.loat.*;
import aprove.input.Programs.pushdownSMT.*;
import aprove.input.Programs.t2.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;
import aprove.verification.oldframework.SMT.Solver.Z3.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 *
 */
public class KoAT2TerminationProcessor extends Processor.ProcessorSkeleton {

    private static class KoATExecutionException extends Exception {

        private static final long serialVersionUID = -594771260391616880L;

        public KoATExecutionException(String errorMessage, Throwable cause) {
            super(errorMessage, cause);
        }
    }

    /**
     * If true, errors when executing KoAT2 are printed to stderr
     */
    static final boolean PRINT_KOAT_ERRORS_TO_STDERR = true;

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof KoatProblem;
    }

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        assert !Globals.useAssertions || obl instanceof KoatProblem;

        try {
            final File tempFile = writeToFile(obl);
            final List<String> koatCommand = determineKoatCommand(tempFile, aborter);

            Triple<Integer, List<String>, List<String>> koatOutput = ExecHelper.execAndGetExitCode(koatCommand,
                                                                                                   getEnv(),
                                                                                                   aborter);
            int koatExitCode = koatOutput.x;
            List<String> koatStdout = koatOutput.y;

            aborter.checkAbortion();

            if (koatExitCode != 0 && !aborter.isAborted()) {
                throw new KoATExecutionException("Running KoAT2 finished with non-zero exit code " + koatExitCode
                                                 + " when running command: \n"
                                                 + koatCommand + "\n"
                                                 + "the error message is: \n"
                                                 + koatOutput.z,
                                                 null);
            }
            tempFile.delete();

            KoATProof koatProof = KoATProof.createFromOutput(koatCommand, koatStdout);
            String proofMessage = koatProof.message;
            switch (koatProof.status) {
                case YES:
                    return ResultFactory.proved(koatProof);
                case MAYBE:
                    return ResultFactory.unknown(koatProof);
                default:
                    throw new IllegalArgumentException("Invalid YNM value " + koatProof.status);
            }

        } catch (KoATExecutionException e) {
            if (PRINT_KOAT_ERRORS_TO_STDERR) {
                System.err.println(e.getMessage());
            }
            return ResultFactory.error(e.getMessage());
        } catch (IOException | InterruptedException e) {
            // Build a string from the exception and return it as the error
            StringBuilder sb = new StringBuilder();
            sb.append("Unknown error running koat\n");
            sb.append(e.getMessage()).append("\n");
            for (StackTraceElement el : e.getStackTrace()) {
                sb.append(el.toString()).append("\n");
            }

            String errorMessage = sb.toString();
            System.err.println(errorMessage);
            return ResultFactory.error(errorMessage);
        }
    }

    /**
     *
     * @param problem
     * @return
     * @throws IOException
     */
    private File writeToFile(BasicObligation problem) throws IOException {
        String content = "";
        String fileSuffix = "";
        if (problem instanceof KoatProblem) {
            fileSuffix = ".koat";
            content = problem.export(new PLAIN_Util());
        }
        final File tempFile = File.createTempFile("aprove.input.Programs.koat2_", fileSuffix);
        final OutputStream os = new FileOutputStream(tempFile);
        final Writer fileWriter = new OutputStreamWriter(os);
        fileWriter.write(content);
        fileWriter.close();
        return tempFile;
    }


    /**
     * this function specifies the command KoAT2 is called with.
     *
     * @param file
     * @param aborter
     * @return
     * @throws KoATExecutionException
     * @throws InterruptedException
     */
    private List<String> determineKoatCommand(File file, Abortion aborter) throws KoATExecutionException,
                                                                              InterruptedException {
        List<String> parameters = new ArrayList<>();

        // determine the koat file given by the variable KOAT2_PATH
        String koatPathStr = System.getenv("KOAT2_PATH");
        String errorMsg = "Set the 'KOAT2_PATH' environment variable to point to the folder containing the executable koat file";
        String linebreak = System.lineSeparator();
        if (koatPathStr == null) {
            throw new KoATExecutionException("No KoAT2 installation found. " + linebreak + errorMsg, null);
        }
        File koatPath = new File(koatPathStr);
        if (!koatPath.exists() || !koatPath.isDirectory() || !koatPath.canRead()) {
            throw new KoATExecutionException("KOAT2_PATH isn't a readable directory.", null);
        }
        List<String> files = Arrays.asList(koatPath.list());
        if (!files.contains("koat2")) {
            throw new KoATExecutionException("No koat2 found. " + linebreak + errorMsg, null);
        }

        parameters.add(koatPath.getAbsolutePath() + File.separator + "koat2");

        // only try to prove termination
        parameters.add("analyse");
        parameters.add("--termination");
        parameters.add("--cfr=pe");
        parameters.add("-d5");
        parameters.add("--local=mprf,twn");
        parameters.add("-rtermcomp");
        // path to temporary file
        parameters.add("-i");
        parameters.add(file.getAbsolutePath());

        return parameters;
    }

    private Map<String, String> getEnv() {
        Map<String, String> env = new HashMap<>();
        env.put("PATH", System.getenv("PATH"));
        return env;
    }

    public static class KoATProof extends DefaultProof {

        private String message;
        private YNM status;

        /**
         * Constructor for KoAT2 proof result
         *
         * @param message proof message printed by KoAT
         * @param status  proof status
         */
        private KoATProof(final String message, YNM status) {
            this.shortName = "KoAT2";
            this.longName = "Proof of Termination by KoAT2";
            this.message = message;
            this.status = status;
        }

        public void addLog(String log) {
            this.message += log;
        }

        static KoATProof createFromOutput(List<String> command, List<String> output) {
            StringBuilder proofBuilder = new StringBuilder();

            proofBuilder.append("KoAT2 was called with the following command:\n\n");
            for (String c : command) {
                proofBuilder.append(c).append(" ");
            }
            proofBuilder.append("\n\n").append("KoAT2's output was:\n\n");

            YNM conclusion = YNM.MAYBE;
            if (output.contains("YES")) {
                conclusion = YNM.YES;
            }

            Queue<String> koatStdout = new LinkedList<>(output);

            do {
                String currentLine = koatStdout.poll();
                proofBuilder.append(currentLine).append('\n');
            } while (!koatStdout.isEmpty());

            String proofString = proofBuilder.toString();
            if (proofString.isEmpty()) {
                proofString = "No proof given by KOAT";
            }

            return new KoATProof(proofString, conclusion);
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o instanceof HTML_Util ? o.export("<pre style=\"overflow-y:scroll\">" + message + "</pre>")
                                          : o.export(message);
        }

    }
}
