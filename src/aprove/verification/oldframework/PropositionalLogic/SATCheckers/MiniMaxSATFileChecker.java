package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class MiniMaxSATFileChecker implements MaxSATChecker {

    private static final String COMMAND = "minimaxsat1.0";

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.SATCheckers.MiniMaxSATFileChecker");
    //private static final File curDir = new File("/home/kabasci/dimacs/");

    public MiniMaxSATFileChecker() {}

    @Override
    public void setAssumps(Set<Formula<None>> assumps) {
        throw new UnsupportedOperationException("Assumptions currently only supported by MiniSATFileChecker.");
    }

    @Override
    public int[] solve(Formula<None> formula, final Abortion aborter) {
        throw new UnsupportedOperationException("Non-optimized solving not implemented for MiniMaxSAT!");
    }

    @Override
    public int[] solve(Formula<None> formula, Collection<Formula<None>> maxSatFormulas, final Abortion aborter) throws AbortionException {
        String dimacs;
        dimacs = FormulaToDimacsConverter.convertPMax(formula, maxSatFormulas);
        if (MiniMaxSATFileChecker.log.isLoggable(Level.FINEST)) {
            MiniMaxSATFileChecker.log.log(Level.FINE, "CNF length in characters: {0}\n", dimacs.length());
            int nlPos = dimacs.indexOf("\n");
            MiniMaxSATFileChecker.log.fine("First line of DIMACS problem (# vars, # clauses):\n"
                    + dimacs.substring(0, nlPos + 1));
        }
        return this.solve(dimacs, aborter);
    }

    @Override
    public int[] solve(String dimacs, final Abortion aborter) throws AbortionException {
        final Process process;
        File input = null;
        File output = null;
        Scanner sc = null;
        try {
            input = File.createTempFile("aproveMiniMaxSAT", ".dimacs");
            Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(dimacs);
            dimacs = null;
            inputWriter.close();
            input.deleteOnExit();
            //output = File.createTempFile("aproveMiniSAT",".output", curDir);
            output = File.createTempFile("aproveMiniMaxSAT",".output");
            output.deleteOnExit();

            String args = "";

            MiniMaxSATFileChecker.log.log(Level.FINER, "DIMACS to {0}\n",
                    input.getCanonicalPath());
            MiniMaxSATFileChecker.log.log(Level.FINER, "OUTPUT to {0}\n", output.getCanonicalPath());

            //ProcessBuilder pb = new ProcessBuilder(COMMAND, input.getCanonicalPath(), output.getCanonicalPath());
            //pb.redirectErrorStream(true);
            //process = pb.start();
            //process = Runtime.getRuntime().exec(COMMAND + " "+input.getCanonicalPath()+" "+output.getCanonicalPath());
            MiniMaxSATFileChecker.log.log(Level.FINER, "Invoking {0}\n", MiniMaxSATFileChecker.COMMAND + args);
            process = Runtime.getRuntime().exec(MiniMaxSATFileChecker.COMMAND + args + " -F=2 "+
                    input.getCanonicalPath());
            TrackerFactory.process(aborter, process);
            sc = new Scanner(process.getInputStream());
            ArrayList<Integer> resList = new ArrayList<Integer>();
            while (true) {
                String line = sc.nextLine();

                MiniMaxSATFileChecker.log.log(Level.FINEST, "{0}\n", line);
                if (line.startsWith("c")) {
                    continue;
                }
                if (line.startsWith("o")) {
                    continue;
                }
                if (line.startsWith("s UNSATISFIABLE")) {
                    MiniMaxSATFileChecker.log.log(Level.FINE, "MiniMaxSAT says: UNSAT\n");
                    return null;
                }
                if (line.startsWith("s SATISFIABLE")) {
                    MiniMaxSATFileChecker.log.log(Level.FINE, "MiniMaxSAT says: SAT\n");
                    continue;
                }
                if (line.startsWith("s OPTIMUM FOUND")) {
                    MiniMaxSATFileChecker.log.log(Level.FINE, "MiniMaxSAT says: OPTIMUM FOUND\n");
                    continue;
                }
                if (line.startsWith("v ")) {
                    sc = new Scanner(line.substring(2));
                    resList = new ArrayList<Integer>();
                    while (true) {
                        int next = 0;
                        try{
                            next = sc.nextInt();
                        }
                        catch (NoSuchElementException e) {
                            break;
                        }
                        if (next == 0) {
                            break;
                        }
                        resList.add(next);
                    }
                    break;
                }
                assert false;
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
            if (output != null) {
                output.delete();
            }
            if (sc != null) {
                sc.close();
            }
        }
        return null;
    }

    @Override
    public int[] solveCNF(Formula<None> formula, Abortion aborter) {
        throw new UnsupportedOperationException("Dedicated solving for CNFs not implemented.");
    }
}
