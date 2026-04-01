package aprove.verification.dpframework.MCSProblem.satsolver;

import java.io.*;
import java.util.*;

import org.sat4j.core.*;
import org.sat4j.specs.*;

/**
 * SATSolver class for solvers that comply to the I/O format of the
 * SAT Competition / the SAT Race. Their common characteristic is that
 * they all read input from a file and write output to stdout.
 * More on the I/O format, which is used both for the SAT Competition
 * and for the SAT Race:
 *
 * http://www.satcompetition.org/2009/format-solvers2009.html
 *
 * Examples of SAT solvers that should work here are:
 *
 * - MiniSAT 2.2
 * - CryptoMiniSAT
 */
public class SATRaceSolver implements SATSolver {

    private final String COMMAND;
    private final String ARGS;

    /**
     * @param command - name of external executable that will be called
     * @param args - arguments for the command, no leading blank needed
     */
    public SATRaceSolver(final String command, final String args) {
        this.COMMAND = command;
        this.ARGS = args;
    }

    /**
     * @param command - name of external executable that will be called
     *  without any additional args
     */
    public SATRaceSolver(final String command) {
        this(command, "");
    }

    @Override
    public int[] solveFile(final String dimacsFilename) throws SATSolverException {
        Process process = null;
        Scanner sc = null;
        try {
            final String cmdWithArgs =
                (this.ARGS.length() > 0 ? this.COMMAND + " " + this.ARGS : this.COMMAND) + " " + dimacsFilename;
            process = Runtime.getRuntime().exec(cmdWithArgs);
            sc = new Scanner(process.getInputStream());
            IVecInt resVecInt = null;
            while (sc.hasNextLine()) {
                final String line = sc.nextLine();
                if (line.startsWith("c") || line.length() == 0) {
                    // Some solvers like Clasp also like to output empty lines.
                    // It is questionable whether this is okay according to the
                    // specs, but we want to be able to use those solvers, too.
                    continue;
                }
                if (line.startsWith("s UNSATISFIABLE")) {
                    return null;
                }
                if (line.startsWith("s SATISFIABLE")) {
                    continue;
                }
                if (line.startsWith("v ")) {
                    try (final Scanner scLine = new Scanner(line.substring(2))) {
                        if (resVecInt == null) {
                            resVecInt = new VecInt();
                        }
                        while (scLine.hasNextInt()) {
                            final int next = scLine.nextInt();
                            if (next == 0) {
                                break;
                            }
                            resVecInt.push(next);
                        }
                    }
                    continue;
                }
                throw new SATSolverException("Cannot handle SAT solver output: " + line);
            }
            if (resVecInt == null) {
                throw new SATSolverException("No model output");
            }
            final int[] res = new int[resVecInt.size()];
            resVecInt.copyTo(res);
            return res;
        } catch (final NoSuchElementException e) {
            // just fall through to SolverException
        } catch (final IOException e) {
            throw new SATSolverException(e);
        } finally {
            if (sc != null) {
                sc.close();
            }
            if (process != null) {
                process.destroy();
            }
        }
        throw new SATSolverException("SAT solving failed.");
    }
}
