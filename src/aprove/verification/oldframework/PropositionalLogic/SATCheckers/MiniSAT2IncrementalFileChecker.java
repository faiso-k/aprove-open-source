package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * The minisat2 incremental file checker. As there is no "aprove-minisat" in the path as of now,
 * this is hard-wired to my home for the moment.
 * This is of course a big
 * TODO
 * Can be used as a standard SAT-Engine, however upon calling search with an additional
 * boolean argument the conflict database is retained within the minisat process,
 * thus allowing to add additional constraints.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class MiniSAT2IncrementalFileChecker extends AbstractSATChecker {
    private final String COMMAND;

    public MiniSAT2IncrementalFileChecker(final boolean simp) {
        this.COMMAND = (simp) ? "minisat2simpinc" : "minisat2coreinc";
    }

    private Process process;
    private String outputfile;

    @Override
    public int[] solve(final Formula<None> formula, final Abortion aborter) throws AbortionException, SolverException {
        return this.solve(formula, aborter, false);
    }

    public int[] solve(final Formula<None> formula, final Abortion aborter, final boolean keepProcess)
            throws AbortionException, SolverException {
        final String dimacs = FormulaToDimacsConverter.convert(formula, aborter);
        if (AbstractSATChecker.log.isLoggable(Level.FINEST)) {
            AbstractSATChecker.log.log(Level.FINE, "CNF length in characters: {0}\n", dimacs.length());
            final int nlPos = dimacs.indexOf("\n");
            AbstractSATChecker.log.fine("First line of DIMACS problem (# vars, # clauses):\n" + dimacs.substring(0, nlPos + 1));
        }

        File input = null;
        File output = null;
        try {
            //    input = File.createTempFile("aproveMiniSAT",".dimacs", curDir);
            input = File.createTempFile("aproveMiniSAT", ".dimacs");
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(dimacs);
            inputWriter.close();
            input.deleteOnExit();
            //output = File.createTempFile("aproveMiniSAT",".output", curDir);
            output = File.createTempFile("aproveMiniSAT", ".output");
            output.deleteOnExit();
            this.outputfile = output.getCanonicalPath();
            AbstractSATChecker.log.log(Level.FINER, "DIMACS to {0}\n", input.getCanonicalPath());
            AbstractSATChecker.log.log(Level.FINER, "OUTPUT to {0}\n", output.getCanonicalPath());
            final ProcessBuilder pb =
                new ProcessBuilder(this.COMMAND, "-incremental", input.getCanonicalPath(), output.getCanonicalPath());
            pb.redirectErrorStream(true);
            this.process = pb.start();
            //process = Runtime.getRuntime().exec(COMMAND + " "+input.getCanonicalPath()+" "+output.getCanonicalPath());
            TrackerFactory.process(aborter, this.process);

            // XXX - make this call solveKeepObligation instead of duplicating code

            final BufferedReader stdOut = new BufferedReader(new InputStreamReader(this.process.getInputStream()));
            while (true) {
                final String line = stdOut.readLine();
                if (line == null || line.startsWith("-")) {
                    // /[-].*/ is the delimiter symbol for indicating "search step done"
                    break;
                }
                AbstractSATChecker.log.log(Level.FINEST, "{0}\n", line);
            }
            try (Scanner sc = new Scanner(output)) {
                final String result = sc.next();
                if (!sc.hasNext()) {
                    if (!keepProcess) {
                        this.finalize();
                    }
                    throw new SolverException();
                }
                if (!result.equals("SAT")) {
                    if (result.equals("UNSAT")) {
                        if (!keepProcess) {
                            this.finalize();
                        }
                        return null;
                    }
                    assert false;
                }
                AbstractSATChecker.log.log(Level.FINE, "MiniSAT says: {0}\n", result);
                final ArrayList<Integer> resList = new ArrayList<Integer>();
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
                if (!keepProcess) {
                    this.finalize();
                }
                return res;

            } catch (final FileNotFoundException e) {
                if (!keepProcess) {
                    this.finalize();
                }
                throw new SolverException();
            }
        } catch (final NoSuchElementException e) {
            // just return null
        } catch (final IOException e) {
            e.printStackTrace();
        } finally {
            if (input != null) {
                input.delete();
            }
            if (output != null) {
                output.delete();
            }
        }
        if (!keepProcess) {
            this.finalize();
        }
        throw new SolverException();
    }

    // Important: When building this formula, it needs to be labelled.
    // It is required, that
    // any possible new variabled be labelled exactly in succesing order to the last
    // variable of the original formula.
    public int[] solveKeepObligation(final Formula<None> additionalConstraints, final Abortion aborter)
            throws AbortionException {
        final String dimacs = FormulaToDimacsConverter.convert(additionalConstraints, aborter);
        // Now we need to strip the first line of this dimacs string, as
        // only the clauses are relevant here.
        final int index = dimacs.indexOf("\n");
        final String solveStr = dimacs.substring(index + 1);
        final OutputStreamWriter ow = new OutputStreamWriter(this.process.getOutputStream());
        if (this.outputfile == "") {
            return null;
            // not yet started to solve
        }
        final File output = new File(this.outputfile);
        output.deleteOnExit();
        try {
            final Semaphore sem = new Semaphore(1);

            AbstractSATChecker.log.log(Level.FINER, "OUTPUT to {0}\n", output.getCanonicalPath());
            //process = Runtime.getRuntime().exec(COMMAND + " "+input.getCanonicalPath()+" "+output.getCanonicalPath());
            final Thread stdoutThread = new Thread() {
                @Override
                public void run() {
                    BufferedReader stdOut;
                    synchronized (this) {
                        stdOut =
                            new BufferedReader(new InputStreamReader(
                                MiniSAT2IncrementalFileChecker.this.process.getInputStream()));
                    }
                    String line;
                    while (true) {
                        try {
                            line = stdOut.readLine();
                            if (line == null || line.startsWith("-")) {
                                // /[-].*/ is the delimiter symbol for indicating "search step done"
                                sem.drainPermits();
                                break;
                            }
                        } catch (final IOException ex) {
                            sem.drainPermits();
                            break;
                        }
                        synchronized (this) {
                            AbstractSATChecker.log.log(Level.FINEST, "{0}\n", line);
                        }
                    }
                }
            };
            stdoutThread.start();
            ow.write(solveStr + "\ns\n");
            ow.flush();
            while (sem.availablePermits() > 0) {
                // noop
            }
            try (Scanner sc = new Scanner(output)) {
                final String result = sc.next();
                if (!sc.hasNext()) {
                    this.finalize();

                    return null;
                }
                if (!result.equals("SAT")) {
                    if (result.equals("UNSAT")) {
                        this.finalize();
                        return null;
                    }
                    assert false;
                }
                AbstractSATChecker.log.log(Level.FINE, "MiniSAT says: {0}\n", result);
                final ArrayList<Integer> resList = new ArrayList<Integer>();
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
            } catch (final FileNotFoundException e) {
                this.finalize();
                return null;
            }
        } catch (final NoSuchElementException e) {
            // just return null
        } catch (final IOException e) {
        } finally {
            if (output != null) {
                output.delete();
            }
        }
        this.finalize();
        return null;

    }

    @Override
    public void finalize() {
        if (this.process == null) {
            return;
        }
        final OutputStreamWriter ow = new OutputStreamWriter(this.process.getOutputStream());
        try {
            ow.write("q\n");
            ow.flush();
        } catch (final IOException ex) {
            // Fine. the process is yet dead.
        }
        // now - pretty immediate, but this is fine for minisat - the hard way.
        if (this.process != null) {
            this.process.destroy();
        }

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
