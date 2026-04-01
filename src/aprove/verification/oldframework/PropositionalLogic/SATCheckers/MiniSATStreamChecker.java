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
 * This uses a special version of MiniSAT, which will output its proof to stderr, called minisat_proof2stderr
 * It looks for this executable in the PATH
 * In order to build this special version of MiniSAT, apply the following patch to the MiniSAT v1.14 sources:

diff -cr MiniSat_v1.14_orig/Main.C MiniSat_v1.14/Main.C
*** MiniSat_v1.14_orig/Main.C   Tue Jul  5 08:42:54 2005
--- MiniSat_v1.14/Main.C        Wed May 24 12:15:51 2006
***************
*** 213,219 ****
          gzclose(in);
      }
      FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;
!
      if (!S.okay()){
          if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
          reportf("Trivial problem\n");
--- 213,224 ----
          gzclose(in);
      }
      FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;
!
!       //fclose(stdout);
!       if(res == NULL) {
!               res = stderr;
!       }
!
      if (!S.okay()){
          if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
          reportf("Trivial problem\n");

 *
 * If you don't like the summary that MiniSAT usually produces on stdout, uncomment the fclose(stdout) above.
 *
 * @author matraf
 *
 */
public class MiniSATStreamChecker implements SATChecker {

    private static final Logger log =
        Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.SATCheckers.MiniSATStreamChecker");

    @Override
    public int[] solve(final Formula<None> formula, final Abortion aborter) throws AbortionException {
        final String dimacs = FormulaToDimacsConverter.convert(formula, aborter);
        final Process process;
        try {
            /*
            File input = File.createTempFile("aproveMiniSAT",".dimacs");
            Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(dimacs);
            inputWriter.close();
            input.deleteOnExit();
            File output = File.createTempFile("aproveMiniSAT",".output");
            output.deleteOnExit();
            log.log(Level.FINER, "DIMACS to {0}\n", input.getCanonicalPath());
            log.log(Level.FINER, "OUTPUT to {0}\n", output.getCanonicalPath());
            process = Runtime.getRuntime().exec("minisat "+input.getCanonicalPath()+" "+output.getCanonicalPath());
            */

            // XXX DEBUG timing information
            //            long now = System.currentTimeMillis();

            final ProcessBuilder processBuilder = new ProcessBuilder("minisat_proof2stderr");
            process = processBuilder.start();
            TrackerFactory.process(aborter, process);
            try (final Scanner sc = new Scanner(process.getErrorStream())) {
                final BufferedReader stdOut = new BufferedReader(new InputStreamReader(process.getInputStream()));
                final Writer inputWriter = new OutputStreamWriter(process.getOutputStream());
                inputWriter.write(dimacs);
                inputWriter.close();
                //            BufferedReader stdOut = new BufferedReader(new InputStreamReader(process.getInputStream()));
                while (true) {
                    final String line = stdOut.readLine();
                    if (line == null) {
                        break;
                    }
                    MiniSATStreamChecker.log.log(Level.FINEST, "{0}\n", line);
                }
                //            Scanner sc = new Scanner(output);
                final String result = sc.next();
                if (!sc.hasNext()) {
                    return null;
                }

                // XXX DEBUG timing information
                //            now = System.currentTimeMillis() - now;
                //            System.err.println("\t[DEBUG] MiniSAT Stream checker took "+(now/1000.)+" sec.");

                if (!result.equals("SAT")) {
                    if (result.equals("UNSAT")) {
                        return null;
                    }
                    assert false;
                }
                MiniSATStreamChecker.log.log(Level.FINE, "MiniSAT says: {0}\n", result);
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
            }
        } catch (final IOException e) {
        }
        return null;
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
