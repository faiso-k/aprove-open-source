package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * MiniSAT09Z SAT checker
 * The input goes to stdin, the output comes over stdout.
 *
 * You need the executable files "minisat09zcore" and "minisat09zsimp" in an accessible path.
 *
 * @author Andreas Kelle-Emden
 */
public class MiniSAT09ZChecker extends AbstractSATChecker {

    private final static String COMMAND_CORE = "minisat09zcore";
    private final static String COMMAND_SIMP = "minisat09zsimp";
    private final boolean simp;

    public MiniSAT09ZChecker(final boolean simp) {
        this.simp = false;
        /* Note: Up to now MiniSAT 09Z does not return a model if called with simp!
         * So far we cannot use that one. TODO Add support for simp mode later
         */
    }

    @Override
    public void setAssumps(final Set<Formula<None>> assumps) {
    }

    @Override
    public int[] solve(String dimacs, final Abortion aborter) throws AbortionException, SolverException {
        final Process process;
        Scanner sc = null;
        try {

            final String args = "";

            final String command = this.simp ? MiniSAT09ZChecker.COMMAND_SIMP : MiniSAT09ZChecker.COMMAND_CORE;
            AbstractSATChecker.log.log(Level.FINER, "Invoking {0}\n", command + args);
            process = Runtime.getRuntime().exec(command + args);
            TrackerFactory.process(aborter, process);
            aborter.checkAbortion();
            final Writer writer = new OutputStreamWriter(process.getOutputStream());
            writer.write(dimacs);
            writer.flush();
            writer.close();
            dimacs = null;
            aborter.checkAbortion();
            sc = new Scanner(process.getInputStream());
            ArrayList<Integer> resList = null;
            while (sc.hasNextLine()) {
                final String line = sc.nextLine();
                AbstractSATChecker.log.log(Level.FINEST, "{0}\n", line);
                if (line.startsWith("c")) {
                    continue;
                }
                if (line.startsWith("s UNSATISFIABLE")) {
                    AbstractSATChecker.log.log(Level.FINE, "MiniSAT09Z says: UNSAT\n");
                    return null;
                }
                if (line.startsWith("s SATISFIABLE")) {
                    AbstractSATChecker.log.log(Level.FINE, "MiniSAT09Z says: SAT\n");
                    continue;
                }
                if (line.startsWith("v ")) {
                    try (final Scanner scLine = new Scanner(line.substring(2))) {
                        if (resList == null) {
                            resList = new ArrayList<>();
                        }
                        while (scLine.hasNextInt()) {
                            final int next = scLine.nextInt();
                            if (next == 0) {
                                break;
                            }
                            resList.add(next);
                        }
                    }
                    continue;
                }
                aborter.checkAbortion();
                throw new SolverException();
            }
            aborter.checkAbortion();
            if (resList == null) {
                return null;
            }
            final int[] res = new int[resList.size()];
            for (int i = 0; i < res.length; i++) {
                res[i] = resList.get(i);
            }
            return res;
        } catch (final NoSuchElementException e) {
            // just return null
        } catch (final IOException e) {
        } finally {
            if (sc != null) {
                sc.close();
            }
        }
        throw new SolverException();
    }

    @Override
    public int[] solveCNF(final Formula<None> formula, final Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

}
