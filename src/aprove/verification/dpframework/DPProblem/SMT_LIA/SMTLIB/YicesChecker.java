/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.SMT_LIA.SMTLIB;

import java.io.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Uses Yices as external SMTLIB solver.
 *
 * Tested with Yices 1.0.11.
 *
 * @author noschinski
 *
 */
public class YicesChecker extends AbstractChecker {

    private static final Logger LOG = Logger.getLogger("aprove.verification.dpframework.DPProblem.SMT_LIA.SMTLIB.YicesChecker");

    @Override
    protected YNM callSolver(final String benchmark, final Abortion aborter) throws AbortionException {
        return YicesChecker.callYices(benchmark, aborter);
    }

    public static YNM callYices(final String benchmark, final Abortion aborter) throws AbortionException {
        return YicesChecker.callYices(benchmark, YicesChecker.LOG, aborter);
    }

    public static YNM callYices(final String benchmark, final Logger logger, final Abortion aborter)
            throws AbortionException {
        YNM result;
        Process process = null;
        final ProcessBuilder process_builder = new ProcessBuilder("yices", "-smt");
        try {
            process = process_builder.start();
            TrackerFactory.process(aborter, process);
            final BufferedReader procStdOut = new BufferedReader(new InputStreamReader(process.getInputStream()));
            final BufferedReader procStdErr = new BufferedReader(new InputStreamReader(process.getErrorStream()));
            final Writer procStdIn = new OutputStreamWriter(process.getOutputStream());
            procStdIn.write(benchmark);
            procStdIn.close();

            String procResult = procStdOut.readLine();
            if (procResult != null) {
                procResult = procResult.trim();
            }

            aborter.checkAbortion();
            if ("sat".equals(procResult)) {
                result = YNM.YES;
            } else if ("unsat".equals(procResult)) {
                result = YNM.NO;
            } else {
                logger.log(Level.WARNING,
                    "Yices produced unexpected output: {0}", procResult);
                logger.log(Level.WARNING, "Error message (first line): {0}",
                    procStdErr.readLine());
                logger.log(Level.WARNING, "Input was:\n{0}", benchmark);
                result = YNM.MAYBE;
            }
        } catch(final IOException e) {
            if (!e.toString().equals("java.io.IOException: Stream closed")) {
                logger.log(Level.WARNING, "Yices execution failed: {0}",
                    e.toString());
            }
            result = YNM.MAYBE;
        } finally {
            if (process != null) {
                process.destroy();
            }
        }

        return result;
    }
}
