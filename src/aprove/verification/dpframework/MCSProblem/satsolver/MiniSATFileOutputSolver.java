package aprove.verification.dpframework.MCSProblem.satsolver;

import java.io.*;
import java.util.*;

import org.sat4j.core.*;
import org.sat4j.specs.*;

/**
 * SATSolver implementation designed to work with the external SAT solvers
 * MiniSAT 2.0 and MiniSAT 2.2, as contained in:
 *
 * http://www.minisat.se/downloads/minisat2-070721.zip
 *
 * http://www.minisat.se/downloads/minisat-2.2.0.tar.gz
 *
 * The output of these versions of MiniSAT does not exactly comply to the
 * requirements of SAT competition / SAT race, so we use dedicated Java
 * code to interact with it.
 */
public class MiniSATFileOutputSolver implements SATSolver {

    private final String COMMAND;
    private final String ARGS;

    /**
     * @param command name of the executable to be called
     * @param args string of arguments to be appended to the call
     */
    public MiniSATFileOutputSolver(final String command, final String args) {
        this.COMMAND = command;
        this.ARGS = args;
    }

    /**
     * @param command name of the executable to be called without arguments
     */
    public MiniSATFileOutputSolver(final String command) {
        this(command, "");
    }

    @Override
    public int[] solveFile(final String dimacsFilename) throws SATSolverException {
        File input = null;
        File output = null;
        try {
            input = new File(dimacsFilename);
            output = File.createTempFile("aproveSAT", ".output");
            output.deleteOnExit();
            return this.solve(input, output);
        } catch (final NoSuchElementException e) {
            // fall-through to the SolverException
        } catch (final IOException e) {
            e.printStackTrace();
        } finally {
            if (output != null) {
                output.delete();
            }
        }
        throw new SATSolverException("SAT Solving failed.");
    }

    /**
     * @param input contains a CNF in Dimacs format
     * @param output MiniSAT will write its output to this file
     * @return a model for <code>input</code> if one exists, null otherwise
     * @throws SATSolverException if neither SAT nor UNSAT could be shown
     *  (for a variety of reasons)
     */
    public int[] solve(final File input, final File output) throws SATSolverException {
        final Process process;
        try {
            String[] runMe;
            // beware of putting the empty String in there
            if (this.ARGS.length() > 0) {
                runMe = new String[] {this.COMMAND, this.ARGS, input.getCanonicalPath(), output.getCanonicalPath() };
            } else {
                runMe = new String[] {this.COMMAND, input.getCanonicalPath(), output.getCanonicalPath() };
            }
            try {
                process = Runtime.getRuntime().exec(runMe);
            } catch (final IOException e) {
                throw new SATSolverException(e);
            }
            try (BufferedReader stdOut = new BufferedReader(new InputStreamReader(process.getInputStream()))) {
                while (true) {
                    String line = null;
                    try {
                        line = stdOut.readLine();
                    } catch (final IOException e) {
                        // do nothing. MiniSAT might just be killed because of
                        // some strategy reason.
                    }
                    if (line == null) {
                        break;
                    }
                }
            }
            try (BufferedReader fileReader = new BufferedReader(new FileReader(output))) {
                final String result = fileReader.readLine();
                if (result == null) {
                    throw new SATSolverException("MiniSAT did not report a result");

                }
                if (!result.equals("SAT")) {
                    if (result.equals("UNSAT")) {
                        return null;
                    }
                    throw new SATSolverException("MiniSAT reported neither SAT nor UNSAT");
                }
                final IVecInt resVecInt = new VecInt();
                boolean endOfFile = false;
                while (!endOfFile) {
                    final String line = fileReader.readLine();
                    if (line == null || line.length() == 0) {
                        break;
                    }
                    final String[] numStrings = line.split(" ");
                    final int nums = numStrings.length;
                    for (int i = 0; i < nums; i++) {
                        if (numStrings[i].equals("0")) {
                            endOfFile = true;
                            break;
                        }
                        resVecInt.push(Integer.parseInt(numStrings[i]));
                    }
                }

                final int[] res = new int[resVecInt.size()];

                // System.arraycopy() should be faster than n calls to get()
                resVecInt.copyTo(res);
                return res;
            }
        } catch (final NoSuchElementException e) {
            // just fall through
        } catch (final IOException e) {
            throw new SATSolverException(e);
        }
        throw new SATSolverException("Solving with MiniSAT failed.");
    }
}
