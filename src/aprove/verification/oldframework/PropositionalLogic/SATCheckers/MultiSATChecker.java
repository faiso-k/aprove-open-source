package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * SAT solver combiner.
 * Get a list of different SAT solvers which will try to
 * solve the SAT instance independently.
 * The first result (SAT or UNSAT) will be used.
 */
public class MultiSATChecker extends AbstractSATChecker {

    private List<SATChecker> checkers = null;

    public MultiSATChecker(List<SATChecker> checkers) {
        this.checkers = checkers;
    }

    @Override
    public void setAssumps(Set<Formula<None>> assumps) {
        throw new UnsupportedOperationException("Setting assumptions is not supported by MultiSAT");
    }

    @Override
    public int[] solve(Formula<None> formula, final Abortion aborter) throws AbortionException, SolverException {
        // Converting the formula to both dimacs and reversed dimacs
        // was not successful up to now.
        // But it needs too much time.
        // You may use the framework again later.

        String dimacs;
        //String dimacsReverse;
        //Pair<String, String> dimacsPair = FormulaToDimacsConverter.convertReverse(formula, false);
        dimacs = FormulaToDimacsConverter.convert(formula, aborter);
        //dimacsReverse = dimacs;
        //dimacs = dimacsPair.x;
        //dimacsReverse = dimacsPair.y;
        return this.solve (dimacs, dimacs, aborter);
    }

    @Override
    public int[] solve(String dimacs, Abortion aborter) throws AbortionException, SolverException {
        return this.solve (dimacs, dimacs, aborter);
    }

    public int[] solve(String dimacs, String dimacsReverse, Abortion aborter) throws AbortionException, SolverException {
        aborter.checkAbortion();

        // Use MultithreadedExecutor framework
        // Create work list
        File input = null;
        List<SATWorker> workList = new ArrayList<SATWorker>(this.checkers.size());
        for (SATChecker checker : this.checkers) {
            if (input == null && checker instanceof ExternalSATChecker) {
                try {
                    input = File.createTempFile("aproveExternalSAT", ".dimacs");
                    input.deleteOnExit();
                    Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
                    //long time = System.nanoTime();
                    inputWriter.write(dimacs);
                    //long diff = System.nanoTime()-time;
                    //System.err.println("Writing ExternalSAT file ("+(dimacs.length()/1024)+"kb) need " + diff/1000000 + " ms");
                    dimacs = null;
                    inputWriter.close();
                } catch (IOException e) {
                    input = null;
                }
            }
            workList.add(new SATWorker(checker, dimacs, input));
        }

        aborter.checkAbortion();

        // ...and on we go
        SATWorker worker = MultithreadedExecutor.execute(workList, aborter);

        if (worker != null) {
            return worker.getResult();
        } else {
            // Oh no, all solvers failed
            throw new SolverException();
        }
    }

    @Override
    public int[] solveCNF(Formula<None> formula, Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }


    private static class SATWorker implements AbortableRunnable {

        private final SATChecker myChecker;
        private final String     dimacs;
        private final File       input;
        private int[]      result;

        public SATWorker(SATChecker myChecker, String dimacs, File input) {
            this.myChecker = myChecker;
            this.dimacs    = dimacs;
            this.input     = input;
        }

        @Override
        public WorkStatus execute(Abortion aborter) throws AbortionException {
            try{
                if (this.input != null && this.myChecker instanceof ExternalSATChecker) {
                    this.result = ((ExternalSATChecker)this.myChecker).solve(this.input, aborter);
                } else {
                    this.result = this.myChecker.solve(this.dimacs, aborter);
                }
                return WorkStatus.FINISH;
            } catch (SolverException e) {
                return WorkStatus.CONTINUE;
            }
        }

        public int[] getResult() {
            return this.result;
        }
    }
}
