package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Clasp SAT checker
 * The input goes to stdin, the output comes over stdout.
 *
 * You need an executable file "clasp" in an accessible path.
 *
 * @author Andreas Kelle-Emden
 */
public class SapperlotChecker extends AbstractSATChecker {

    private final static String COMMAND = "SApperloT";

    public SapperlotChecker() {
    }

    @Override
    public void setAssumps(final Set<Formula<None>> assumps) {
    }

    @Override
    public int[] solve(String dimacs, final Abortion aborter) throws AbortionException, SolverException {
        Process process = null;
        Scanner sc = null;
        File input = null;
        try {

            final String args = " -print-console=no ";

            aborter.checkAbortion();
            try {
                input = File.createTempFile("aproveSApperloT", ".dimacs");
                input.deleteOnExit();
                final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
                inputWriter.write(dimacs);
                dimacs = null;
                inputWriter.close();
            } catch (final IOException e) {
                e.printStackTrace();
                return null;
            }
            aborter.checkAbortion();
            AbstractSATChecker.log.log(Level.FINER, "Invoking {0}\n", SapperlotChecker.COMMAND + args);
            process = Runtime.getRuntime().exec(SapperlotChecker.COMMAND + args + input.getCanonicalPath());
            TrackerFactory.process(aborter, process);
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
                    AbstractSATChecker.log.log(Level.FINE, "SApperloT says: UNSAT\n");
                    return null;
                }
                if (line.startsWith("s SATISFIABLE")) {
                    AbstractSATChecker.log.log(Level.FINE, "SApperloT says: SAT\n");
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
            if (process != null) {
                process.destroy();
            }
            if (input != null) {
                input.delete();
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
