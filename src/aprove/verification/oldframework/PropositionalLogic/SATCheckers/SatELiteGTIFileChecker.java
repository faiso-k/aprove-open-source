/* TODO
 * This class does not check for abortions itself.
 * That may end up in some trouble if the solver is aborted.
 * Someone should maybe check if this class is okay or if it even is used anymore
 *
 * -- thetux
 */

package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class SatELiteGTIFileChecker implements SATChecker {

    private static final Logger log =
        Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.SATCheckers.SatELiteGTIFileChecker");

    @Override
    public int[] solve(final Formula<None> formula, final Abortion aborter) throws SolverException, AbortionException {
        final String dimacs = FormulaToDimacsConverter.convert(formula, aborter);
        try {
            final File input = File.createTempFile("aproveSatELiteGTI", ".dimacs");
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(dimacs);
            inputWriter.close();
            input.deleteOnExit();
            SatELiteGTIFileChecker.log.log(Level.FINER, "DIMACS to {0}\n", input.getCanonicalPath());
            final Process process = Runtime.getRuntime().exec("SatELiteGTI " + input.getCanonicalPath());
            TrackerFactory.process(aborter, process);
            try (final Scanner sc = new Scanner(process.getInputStream())) {
                ArrayList<Integer> resList = null;
                while (sc.hasNextLine()) {
                    final String line = sc.nextLine();
                    SatELiteGTIFileChecker.log.log(Level.FINEST, "{0}\n", line);
                    if (line.startsWith("c")) {
                        continue;
                    }
                    if (line.startsWith("s UNSATISFIABLE")) {
                        SatELiteGTIFileChecker.log.log(Level.FINE, "SatELiteGTI says: UNSAT\n");
                        return null;
                    }
                    if (line.startsWith("s SATISFIABLE")) {
                        SatELiteGTIFileChecker.log.log(Level.FINE, "SatELiteGTI says: SAT\n");
                        resList = new ArrayList<>();
                        if (sc.next().equals("v")) {
                            while (true) {
                                final int next = sc.nextInt();
                                if (next == 0) {
                                    break;
                                }
                                resList.add(next);
                            }
                            final int[] res = new int[resList.size()];
                            for (int i = 0; i < res.length; i++) {
                                res[i] = resList.get(i);
                            }
                            return res;
                        } else {
                            assert false;
                        }
                        break;
                    }
                    assert false;
                }
                return null;
            }
        } catch (final NoSuchElementException e) {
            // just return null
        } catch (final IOException e) {
        }
        throw new SolverException();
    }

    @Override
    public int[] solveCNF(final Formula<None> formula, final Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void setAssumps(final Set<Formula<None>> assumps) {
        // Nothing to be done.

    }

    @Override
    public int[] solve(final String dimacs, final Abortion aborter) throws AbortionException {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Not yet implemented");
    }

}
