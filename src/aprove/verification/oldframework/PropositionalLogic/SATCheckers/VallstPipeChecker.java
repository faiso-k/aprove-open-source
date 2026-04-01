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

public class VallstPipeChecker implements SATChecker {

    private static final Logger log =
        Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.SATCheckers.VallstPipeChecker");

    @Override
    public int[] solve(final Formula<None> formula, final Abortion aborter) throws SolverException, AbortionException {
        try {
            final Process process = Runtime.getRuntime().exec("vallst -v0 -o -");
            TrackerFactory.process(aborter, process);
            final Writer writer = new OutputStreamWriter(process.getOutputStream());
            final String dimacs = FormulaToDimacsConverter.convert(formula, aborter);
            while (true) {
                writer.write(dimacs);
                break;
            }
            writer.flush();
            writer.close();
            try (final Scanner sc = new Scanner(process.getInputStream())) {
                ArrayList<Integer> resList = null;
                if (sc.hasNextInt()) {

                    resList = new ArrayList<>();
                    while (sc.hasNextInt()) {
                        final int next = sc.nextInt();
                        resList.add(next);
                    }
                    VallstPipeChecker.log.log(Level.FINE, "Vallst says: SAT\n");
                } else {
                    VallstPipeChecker.log.log(Level.FINE, "Vallst says: UNSAT\n");
                    return null;
                }
                final int[] res = new int[resList.size()];
                for (int i = 0; i < res.length; i++) {
                    res[i] = resList.get(i);
                }
                return res;
            }
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
        throw new UnsupportedOperationException("Not yet implemented");
    }

}
