package aprove.verification.oldframework.Algebra.Polynomials.PBSearch.PBCheckers;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.PBSearch.*;

/**
 * Should work with any PB evaluation compliant solver.
 * That means (among other things) that the solver reads
 * from a file and writes to stdout.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class PBFileChecker implements PBChecker {

    private static final Logger log =
        Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.PBSearch.PBCheckers.PBFileChecker");

    private final String command;
    private final boolean timesAsAsterisk;

    public PBFileChecker(final String command, final boolean timesAsAsterisk) {
        this.command = command;
        this.timesAsAsterisk = timesAsAsterisk;
    }

    @Override
    public int[] check(final Collection<SimplePolyConstraint> spcs,
        final SimplePolynomial maximizeMe,
        final int maxVar,
        final Abortion aborter) throws AbortionException {
        String opb = ToOPBConverter.toOPB(spcs, maximizeMe, maxVar, this.timesAsAsterisk, aborter);
        if (opb == null) {
            return null;
        }
        final Process process;
        File input = null;
        try {
            input = File.createTempFile("aprovePB", ".opb");
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(opb);
            inputWriter.close();
            input.deleteOnExit();
            opb = null;
            PBFileChecker.log.log(Level.FINER, "OPB to {0}\n", input.getCanonicalPath());
            PBFileChecker.log.log(Level.FINER, "Invoking {0}\n", this.command);
            //ProcessBuilder pb = new ProcessBuilder(COMMAND, input.getCanonicalPath(), output.getCanonicalPath());
            //pb.redirectErrorStream(true);
            //process = pb.start();
            //process = Runtime.getRuntime().exec(COMMAND + " "+input.getCanonicalPath()+" "+output.getCanonicalPath());
            process = Runtime.getRuntime().exec(this.command + " " + input.getCanonicalPath());
            TrackerFactory.process(aborter, process);
            final BufferedReader stdOut = new BufferedReader(new InputStreamReader(process.getInputStream()));

            int[] res = null;
            boolean success = false;
            while (true) {
                final String line = stdOut.readLine();
                if (line == null) {
                    break;
                } else if (line.startsWith("c")) {
                    PBFileChecker.log.log(Level.FINEST, "{0}\n", line);
                } else if (line.startsWith("s")) {
                    final String resultType = line.substring(2).trim();
                    if (resultType.equals("SATISFIABLE") || resultType.equals("OPTIMUM FOUND")) {
                        PBFileChecker.log.log(Level.FINEST, this.command + " says: {0}\n", line);
                        success = true;
                    } else { // UNSATISFIABLE / UNKNOWN
                        PBFileChecker.log.log(Level.FINEST, this.command + " says: {0}\n", line);
                        stdOut.close();
                        process.destroy();
                        return null;
                    }
                } else if (line.startsWith("v")) {
                    try (final Scanner sc = new Scanner(line)) {
                        sc.next(); // ignore the v, it has served its purpose
                        if (res == null) {
                            res = new int[maxVar + 1];
                        }
                        while (sc.hasNext()) {
                            final String current = sc.next();
                            final boolean neg = current.startsWith("-");
                            final int offset = neg ? 2 : 1; // we skip the 'x'
                            final int value = Integer.parseInt(current.substring(offset));
                            res[value] = neg ? -value : value;
                        }
                    }
                } else if (line.startsWith("o")) {
                    PBFileChecker.log.log(Level.FINEST, "{0}\n", line);
                }
                /*
                else {
                    if (Globals.useAssertions) {
                        // no ("o " + something) lines, please!
                        // we only check satisfiability.
                        assert false;
                    }
                } */
            }

            // clean up
            stdOut.close();
            process.destroy();

            if (success) {
                return res;
            } else if (res != null) {
                PBFileChecker.log.config("The PB solver says that it has not found a model, but it has output one!\n");
                return null;
            } else {
                return null;
            }
        } catch (final NoSuchElementException e) {
            // just return null
        } catch (final IOException e) {
            if (PBFileChecker.log.isLoggable(Level.WARNING)) {
                PBFileChecker.log.log(Level.WARNING, e.toString() + "\n");
                for (final StackTraceElement ste : e.getStackTrace()) {
                    PBFileChecker.log.log(Level.WARNING, "            " + ste.toString() + "\n");
                }
            }
            //e.printStackTrace();
        } finally {
            if (input != null) {
                input.delete();
            }
        }
        return null;
    }
}
