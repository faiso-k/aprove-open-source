package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.net.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Generic SAT checker class for externally started SAT solvers.
 * You can specify the command and the argument pattern for the solver.
 * The argument pattern must include the two tags &#60;input&#62; and &#60;output&#62;
 * to define in which way the names of the temporary input and output files will be parsed
 * to the solver executable.<br>
 * <br>
 * Example: <br>
 * set command to "minisat2core" and argumentPattern to "<input> <output>" to
 * call MiniSAT.
 *
 * @author Andreas Kelle-Emden
 */
public class ExternalSATChecker extends AbstractSATChecker {

    private final String command;
    private final String argumentPattern;

    public ExternalSATChecker(final String command, final String argumentPattern) {
        this.command = command;
        this.argumentPattern = argumentPattern;
    }

    @Override
    public void setAssumps(final Set<Formula<None>> assumps) {
    }

    @Override
    public int[] solve(final Formula<None> formula, final Abortion aborter) throws AbortionException, SolverException {

        final String dimacsOrIscas = FormulaToDimacsConverter.convert(formula, aborter);
        return this.solve(dimacsOrIscas, aborter);
    }

    @Override
    public int[] solve(String dimacs, final Abortion aborter) throws AbortionException, SolverException {

        File input = null;
        try {
            input = File.createTempFile("aproveExternalSAT", ".dimacs");
            input.deleteOnExit();
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            //long time = System.nanoTime();
            inputWriter.write(dimacs);
            //long diff = System.nanoTime()-time;
            //System.err.println("Writing ExternalSAT file ("+(dimacs.length()/1024)+"kb) need " + diff/1000000 + " ms");
            dimacs = null;
            inputWriter.close();
            aborter.checkAbortion();
            return this.solve(input, aborter);
        } catch (final IOException e) {
        } finally {
            if (input != null) {
                input.delete();
                input = null;
            }
        }
        throw new SolverException();
    }

    public int[] solve(File input, final Abortion aborter) throws AbortionException, SolverException {

        File output = null;
        try {
            aborter.checkAbortion();

            output = File.createTempFile("aproveExternalSAT", ".output");
            output.deleteOnExit();

            final Socket spawner = ExternalSpawner.getSocket();
            final Writer commandWriter = new OutputStreamWriter(spawner.getOutputStream());
            AbstractSATChecker.log.log(Level.FINER, "Invoking {0}\n", this.command + this.argumentPattern);
            String newArgs = this.argumentPattern.replaceFirst("<input>", input.getCanonicalPath());
            newArgs = newArgs.replaceFirst("<output>", output.getCanonicalPath());
            commandWriter.write(this.command + " " + newArgs + "\n");
            commandWriter.flush();
            final BufferedReader stdOut = new BufferedReader(new InputStreamReader(spawner.getInputStream()));
            final int pid = Integer.parseInt(stdOut.readLine());
            TrackerFactory.processByPID(aborter, pid);
            aborter.checkAbortion();
            while (true) {
                String line = null;
                try {
                    line = stdOut.readLine();
                } catch (final IOException e) {
                    // do nothing. MiniSAT might just be killed because of
                    // some strategy reason.
                }
                if (line == null) {
                    break;
                }
                if (AbstractSATChecker.log.isLoggable(Level.FINEST)) {
                    AbstractSATChecker.log.log(Level.FINEST, "{0}\n", line);
                }
            }
            stdOut.close();
            aborter.checkAbortion();
            try (BufferedReader fileReader = new BufferedReader(new FileReader(output))) {
                final String result = fileReader.readLine();
                if (result == null) {
                    throw new SolverException(); // No result here!= MINISAT must have been killed (or some error occured)
                }
                if (!result.equals("SAT")) {
                    if (result.equals("UNSAT")) {
                        return null;
                    }
                    assert false;
                }
                aborter.checkAbortion();
                AbstractSATChecker.log.log(Level.FINE, this.command + " says: {0}\n", result);
                final ArrayList<Integer> resList = new ArrayList<Integer>();
                boolean endOfFile = false;
                while (!endOfFile) {
                    final String line = fileReader.readLine();
                    if (line == null || line.length() == 0) {
                        break;
                    }
                    final String[] numStrings = line.split(" ");
                    final int nums = numStrings.length;
                    for (int i = 0; i < nums; i++) {
                        if (numStrings[i].equals("0")) {
                            endOfFile = true;
                            break;
                        }
                        resList.add(Integer.parseInt(numStrings[i]));
                    }
                }

                final int[] res = new int[resList.size()];
                for (int i = 0; i < res.length; i++) {
                    res[i] = resList.get(i);
                }
                aborter.checkAbortion();
                return res;
            }
        } catch (final NoSuchElementException e) {
            // just return null
        } catch (final IOException e) {
        } finally {
            if (input != null) {
                input.delete();
                input = null;
            }
            if (output != null) {
                output.delete();
                output = null;
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
