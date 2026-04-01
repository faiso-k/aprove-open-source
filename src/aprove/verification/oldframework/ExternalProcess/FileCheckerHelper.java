package aprove.verification.oldframework.ExternalProcess;

import java.io.*;
import java.util.*;

import aprove.strategies.Abortions.*;

/**
 * Base class for building sane file checkers
 *
 * @author Karsten Behrmann
 * @version $Id$
 */
public abstract class FileCheckerHelper {

    public static <T> T checkWithGivenFiles(
        final String problem,
        final Abortion abortion,
        final Checker<T> checker,
        final String problemFilename,
        final String solutionFilename) throws AbortionException
    {
        File problemFile, solutionFile = null;
        try {
            abortion.checkAbortion();
            problemFile = new File(problemFilename);
            final OutputStreamWriter wr = new OutputStreamWriter(new FileOutputStream(problemFile));
            wr.write(problem);
            wr.close();

            abortion.checkAbortion();
            solutionFile = new File(solutionFilename);
            final BufferedReader solutionReader = new BufferedReader(new FileReader(solutionFile));
            final T result = checker.readResult(solutionReader);
            solutionReader.close();
            return result;
        } catch (final IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return null;
        }
    }

    public static <T> T checkWithFiles(
        final String problem,
        final Abortion abortion,
        final FileChecker<T> checker,
        final String program,
        final String... args) throws AbortionException
    {
        return FileCheckerHelper.checkWithFileInput(
            problem,
            abortion,
            checker,
            program,
            args,
            checker.getTempPrefix(),
            checker.getInputTempSuffix(),
            checker.getOutputTempSuffix());
    }

    public static <T> T checkWithStdout(
        final String problem,
        final Abortion abortion,
        final StdoutChecker<T> checker,
        final String program,
        final String... args) throws AbortionException
    {
        return FileCheckerHelper.checkWithFileInput(
            problem,
            abortion,
            checker,
            program,
            args,
            checker.getTempPrefix(),
            checker.getInputTempSuffix(),
            null);
    }

    /**
     * Run a program through an external checker that reads from standard input
     * and writes the solution to standard output.
     *
     * Care should be taken with the sizes of the pipes, the external program
     * must first read stdin until end-of-file before outputting, or we risk
     * a deadlock situation.
     *
     * @param <T> The type of result returned
     * @param problem The problem passed to the checker, as a string
     * @param abortion An aborter, in case we run out of time
     * @param checker The object that will read output and return a result
     * Usually, callers will implement this interface and pass a this-reference
     * @return The result that the checker object found, or null on error
     * @throws AbortionException if we should abort
     */
    public static <T> T checkWithPipes(
        final String problem,
        final Abortion abortion,
        final Checker<T> checker,
        final String cmdline) throws AbortionException
    {
        abortion.checkAbortion();

        try {
            final Process process = Runtime.getRuntime().exec(cmdline);
            TrackerFactory.process(abortion, process);

            final OutputStreamWriter wr = new OutputStreamWriter(process.getOutputStream());
            wr.write(problem);
            wr.close();

            final BufferedReader solution = new BufferedReader(new InputStreamReader(process.getInputStream()));
            final T result = checker.readResult(solution);
            solution.close();

            return result;
        } catch (final IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return null;
        }

    }

    private static <T> T checkWithFileInput(
        final String problem,
        final Abortion abortion,
        final Checker<T> checker,
        final String program,
        final String[] args,
        final String tempPrefix,
        final String inputSuffix,
        final String outputSuffix) throws AbortionException
    {
        File problemFile, solutionFile = null;
        try {
            problemFile = File.createTempFile(tempPrefix, inputSuffix);
            problemFile.deleteOnExit();
            final OutputStreamWriter wr = new OutputStreamWriter(new FileOutputStream(problemFile));
            wr.write(problem);
            wr.close();
        } catch (final IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return null;
        }

        try {
            final List<String> command = new ArrayList<String>();
            command.add(program);
            for (final String arg : args) {
                command.add(arg);
            }
            command.add(problemFile.getCanonicalPath());

            if (outputSuffix != null) {
                solutionFile = File.createTempFile(tempPrefix, outputSuffix);
                solutionFile.deleteOnExit();
                command.add(solutionFile.getCanonicalPath());
            }

            abortion.checkAbortion();

            final Process process = new ProcessBuilder(command).start();
            TrackerFactory.process(abortion, process);

            BufferedReader solution;
            if (outputSuffix == null) {
                solution = new BufferedReader(new InputStreamReader(process.getInputStream()));
            } else {
                // We need to wait until the program is done,
                // else we'll just read a newly-created empty file
                try {
                    process.waitFor();
                } catch (final InterruptedException e) {
                    process.destroy();
                    return null;
                }
                solution = new BufferedReader(new FileReader(solutionFile));
            }

            final T result = checker.readResult(solution);
            solution.close();
            return result;
        } catch (final IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return null;
        }
    }

}
