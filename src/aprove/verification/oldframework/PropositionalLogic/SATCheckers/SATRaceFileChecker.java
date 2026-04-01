package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import org.sat4j.core.*;
import org.sat4j.specs.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * SATSolver class for solvers that comply to the I/O format of the
 * SAT Competition / the SAT Race. Their common characteristic is that
 * they all read input from a file and write output to stdout.
 * More on the I/O format, which is used both for the SAT Competition
 * and for the SAT Race:
 *
 * http://www.satcompetition.org/2009/format-solvers2009.html
 *
 * An example of a SAT solver that should work here is:
 *
 * - CryptoMiniSAT
 */
public class SATRaceFileChecker extends AbstractSATChecker {

    private final String COMMAND;
    private final String ARGS;

    /**
     * @param command - name of external executable that will be called
     * @param args - arguments for the command, no leading blank needed
     */
    public SATRaceFileChecker(final String command, final String args) {
        this.COMMAND = command;
        this.ARGS = args;
    }

    /**
     * @param command - name of external executable that will be called
     *  without any additional args
     */
    public SATRaceFileChecker(final String command) {
        this(command, "");
    }

    @Override
    public int[] solve(String dimacs, final Abortion aborter) throws AbortionException, SolverException {
        File input = null;

        try {
            aborter.checkAbortion();
            input = File.createTempFile("aproveSATRaceFile", ".dimacs");
            input.deleteOnExit();
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            //            long time = System.nanoTime();
            inputWriter.write(dimacs);
            dimacs = null;
            inputWriter.flush();
            inputWriter.close();
            //            long diff = System.nanoTime()-time;
            //            System.err.println("Writing DIMACS file ("+(dimacs.length()/1024)+" kB) needed " + diff + " ns");
            aborter.checkAbortion();
            return this.solveFile(input, aborter);
        } catch (final NoSuchElementException e) {
            // just fall through to SolverException
        } catch (final IOException e) {
            e.printStackTrace();
        } finally {
            if (input != null) {
                input.delete();
            }
        }
        throw new SolverException();

    }


    public int[] solveFile(final File dimacsInputFile, final Abortion aborter) throws SolverException {
        Process process = null;
        Scanner sc = null;
        try {
            String dimacsFilename = dimacsInputFile.getCanonicalPath();
            final String cmdWithArgs =
                (this.ARGS.length() > 0 ? this.COMMAND + " " + this.ARGS : this.COMMAND) + " " + dimacsFilename;
            AbstractSATChecker.log.log(Level.FINER, "Invoking {0}\n", cmdWithArgs);
            process = Runtime.getRuntime().exec(cmdWithArgs);
            TrackerFactory.process(aborter, process);
            aborter.checkAbortion();
            sc = new Scanner(process.getInputStream());
            IVecInt resVecInt = null;
            while (sc.hasNextLine()) {
                final String line = sc.nextLine();
                AbstractSATChecker.log.log(Level.FINEST, "{0}\n", line);
                if (line.startsWith("c") || line.length() == 0) {
                    // Some solvers like Clasp also like to output empty lines.
                    // It is questionable whether this is okay according to the
                    // specs, but we want to be able to use those solvers, too.
                    continue;
                }
                if (line.startsWith("s UNSATISFIABLE")) {
                    AbstractSATChecker.log.log(Level.FINE, "{0} says: UNSAT\n", this.COMMAND);
                    return null;
                }
                if (line.startsWith("s SATISFIABLE")) {
                    AbstractSATChecker.log.log(Level.FINE, "{0} says: SAT\n", this.COMMAND);
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
                aborter.checkAbortion();
                throw new SolverException("Cannot handle SAT solver output: " + line);
            }
            aborter.checkAbortion();
            if (resVecInt == null) {
                throw new SolverException("No model output");
            }
            final int[] res = new int[resVecInt.size()];
            resVecInt.copyTo(res);
            return res;
        } catch (final NoSuchElementException e) {
            // just fall through to SolverException
        } catch (final IOException e) {
        } finally {
            if (sc != null) {
                sc.close();
            }
            if (process != null) {
                process.destroy();
            }
        }
        throw new SolverException("SAT solving failed.");
    }

    @Override
    public void setAssumps(final Set<Formula<None>> assumps) {
        throw new UnsupportedOperationException("This particular SATRaceChecker with command " + this.COMMAND
            + " does not support setting assumptions.");
    }

    @Override
    public int[] solveCNF(final Formula<None> formula, final Abortion aborter) {
        throw new UnsupportedOperationException("CNF solving is not yet implemented.");
    }
}
