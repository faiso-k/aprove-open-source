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

/**
 * @version $Id$
 */
public class RSATFileChecker implements SATChecker {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.SATCheckers.RSATFileChecker");

    @Override
    public int[] solve(Formula<None> formula, Abortion aborter)
            throws AbortionException {
        String dimacs = FormulaToDimacsConverter.convert(formula, aborter);
        Scanner sc = null;
        File input = null;
        try {
            input = File.createTempFile("aproveRSAT",".dimacs");
            Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(dimacs);
            inputWriter.close();
            input.deleteOnExit();
            RSATFileChecker.log.log(Level.FINER, "DIMACS to {0}\n", input.getCanonicalPath());
            //Process process = Runtime.getRuntime().exec("rsat_1_03_linux "+input.getCanonicalPath()+" yes");
            Process process = Runtime.getRuntime().exec("rsat "+input.getCanonicalPath()+" -s");
            TrackerFactory.process(aborter, process);
            sc = new Scanner(process.getInputStream());
            ArrayList<Integer> resList = null;
            while (sc.hasNextLine()) {
                String line = sc.nextLine();
                RSATFileChecker.log.log(Level.FINEST, "{0}\n", line);
                if (line.startsWith("c")) {
                    continue;
                }
                if (line.startsWith("s UNSATISFIABLE")) {
                    RSATFileChecker.log.log(Level.FINE, "RSAT says: UNSAT\n");
                    return null;
                }
                if (line.startsWith("s SATISFIABLE")) {
                    RSATFileChecker.log.log(Level.FINE, "RSAT says: SAT\n");
                    continue;
                }
                if (line.startsWith("v ")) {
                    sc = new Scanner(line.substring(2));
                    resList = new ArrayList<Integer>();
                    while (true) {
                        int next = sc.nextInt();
                        if (next == 0) {
                            break;
                        }
                        resList.add(next);
                    }
                    break;
                }
                assert false;
            }
            if (resList == null) {
                return null;
            }
            int[] res = new int[resList.size()];
            for (int i = 0; i < res.length; i++) {
                res[i] = resList.get(i);
            }
            return res;
        } catch (NoSuchElementException e) {
            // just return null
        } catch (IOException e) {
        } finally {
            if (input != null) {
                input.delete();
            }
            if (sc != null) {
                sc.close();
            }
        }
        return null;
    }

    @Override
    public int[] solveCNF(Formula<None> formula, Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void setAssumps(Set<Formula<None>> assumps) {
        // Nothing to be done.

    }

    @Override
    public int[] solve(String dimacs, Abortion aborter)
            throws AbortionException {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Not yet implemented");
    }
}
