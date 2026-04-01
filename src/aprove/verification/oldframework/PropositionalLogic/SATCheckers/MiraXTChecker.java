package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * MiraXT SAT checker
 * The input goes to a temp file, the output comes over stdout.
 *
 * @author Andreas Kelle-Emden
 */
public class MiraXTChecker extends AbstractSATChecker {

    private final String COMMAND_CORE = "MiraXT";
    private final String COMMAND_SIMP = "MiraXTSimp";

    private int numThreads = 1;
    private String command = this.COMMAND_SIMP;

    public MiraXTChecker(int numThreads, boolean simp) {
        this.numThreads = numThreads;
        this.command = simp ? this.COMMAND_SIMP : this.COMMAND_CORE;
    }

    @Override
    public void setAssumps(Set<Formula<None>> assumps) {
    }

    @Override
    public int[] solve(String dimacs, final Abortion aborter) throws AbortionException, SolverException {
        final Process process;
        File input = null;
        Scanner sc = null;
        try {
            aborter.checkAbortion();
            input = File.createTempFile("aproveMiraXT", ".dimacs");
            input.deleteOnExit();
            Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(dimacs);
            dimacs = null;
            inputWriter.close();
            aborter.checkAbortion();

            String args = "";

            AbstractSATChecker.log.log(Level.FINER, "DIMACS to {0}\n",
                    input.getCanonicalPath());

            //ProcessBuilder pb = new ProcessBuilder(COMMAND, input.getCanonicalPath(), output.getCanonicalPath());
            //pb.redirectErrorStream(true);
            //process = pb.start();
            //process = Runtime.getRuntime().exec(COMMAND + " "+input.getCanonicalPath()+" "+output.getCanonicalPath());
            AbstractSATChecker.log.log(Level.FINER, "Invoking {0}\n", this.command + args);
            process = Runtime.getRuntime().exec(this.command + args + " "+
                    input.getCanonicalPath()+" "+this.numThreads);
            TrackerFactory.process(aborter, process);
            aborter.checkAbortion();
            sc = new Scanner(process.getInputStream());
            ArrayList<Integer> resList = null;
            while (sc.hasNextLine()) {
                String line = sc.nextLine();
                AbstractSATChecker.log.log(Level.FINEST, "{0}\n", line);
                if (line.startsWith("c")) {
                    continue;
                }
                if (line.startsWith("s UNSATISFIABLE")) {
                    AbstractSATChecker.log.log(Level.FINE, "MiraXT says: UNSAT\n");
                    return null;
                }
                if (line.startsWith("s SATISFIABLE")) {
                    AbstractSATChecker.log.log(Level.FINE, "MiraXT says: SAT\n");
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
                aborter.checkAbortion();
                throw new SolverException();
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
        throw new SolverException();
    }

    @Override
    public int[] solveCNF(Formula<None> formula, Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

}
