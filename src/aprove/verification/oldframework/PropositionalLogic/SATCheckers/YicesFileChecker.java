package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class YicesFileChecker implements SATChecker {

    protected Set<Formula<None>> assumps = new LinkedHashSet<Formula<None>>();
    protected boolean hasAssumps = false;

    private static final Logger log =
        Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.SATCheckers.MiniSATFileChecker");

    //private static final File curDir = new File("/home/kabasci/dimacs/");

    public YicesFileChecker() {
    }

    @Override
    public void setAssumps(final Set<Formula<None>> assumps) {
        this.assumps = assumps;
    }

    @Override
    public int[] solve(final Formula<None> formula, final Abortion aborter) throws AbortionException, SolverException {
        aborter.checkAbortion();
        final String dimacs = FormulaToDimacsConverter.convert(formula, aborter);

        return this.solve(dimacs, aborter);
    }

    @Override
    public int[] solve(String dimacs, final Abortion aborter) throws AbortionException, SolverException {

        try {
            final File input = File.createTempFile("aproveYicesSAT", ".dimacs");
            input.deleteOnExit();
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(dimacs);
            dimacs = null;
            inputWriter.close();
            aborter.checkAbortion();
            YicesFileChecker.log.log(Level.FINER, "Invoking yices -d -e " + input.getCanonicalPath());
            final Process process = Runtime.getRuntime().exec("yices -d -e " + input.getCanonicalPath());
            TrackerFactory.process(aborter, process);

            try (final Scanner sc = new Scanner(process.getInputStream())) {
                ArrayList<Integer> resList = null;
                String resString = "unsat";
                if (sc.hasNextLine()) {
                    resString = sc.nextLine();
                }
                if (!resString.equals("sat")) {
                    YicesFileChecker.log.log(Level.FINE, "Yices says: " + resString + "\n");
                    if (resString.equals("unsat")) {
                        return null;
                    }
                    // Some error occured
                    throw new SolverException();
                }
                if (sc.hasNextInt()) {

                    resList = new ArrayList<>();
                    while (sc.hasNextInt()) {
                        final int next = sc.nextInt();
                        resList.add(next);
                    }
                    YicesFileChecker.log.log(Level.FINE, "Yices says: SAT\n");
                } else {
                    // Some other error occured
                    throw new SolverException();
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

}
