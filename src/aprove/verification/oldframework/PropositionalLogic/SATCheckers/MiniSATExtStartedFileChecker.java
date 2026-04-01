package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.net.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class MiniSATExtStartedFileChecker extends AbstractSATChecker {

    private final String COMMAND;

    private final boolean tseitin;

    private final boolean xorClauses;

    protected Set<Formula<None>> assumps = new LinkedHashSet<Formula<None>>();
    protected boolean hasAssumps = false;

    public MiniSATExtStartedFileChecker(
        final int version,
        final boolean simp,
        final boolean assumps,
        final boolean tseitin,
        final boolean xorClauses)
    {
        String command = "minisat";
        command += version;
        if (version >= 2) {
            if (assumps) {
                command += "assumps";
                this.hasAssumps = true;
            } else if (simp) {
                command += "simp";
            } else {
                command += "core";
            }
        }
        if (MiniSATExtStartedFileChecker.found(command)) {
            this.COMMAND = command;
        } else if (MiniSATExtStartedFileChecker.found("minisat")) {
            // fallback (for GUI users?)
            this.COMMAND = "minisat";
        } else {
            System.err.println("Please install minisat2.");
            this.COMMAND = null;
        }
        this.tseitin = tseitin;
        this.xorClauses = xorClauses;
    }

    /**
     * @param cmd the name of the executable
     * @return true if we found some kind of executable with the given name
     */
    static boolean found(final String cmd) {
        final boolean found = false;
        try {
            final Process p = Runtime.getRuntime().exec(cmd + " -h");
            try (
                final BufferedReader bri = new BufferedReader(new InputStreamReader(p.getInputStream()));
                final BufferedReader bre = new BufferedReader(new InputStreamReader(p.getErrorStream()));) {
                while (bri.readLine() != null) {
                    return true;
                }
                bri.close();
                while (bre.readLine() != null) {
                    return true;
                }
            }
        } catch (final IOException e) {
            // ignore
        }
        return false;
    }

    @Override
    public void setAssumps(final Set<Formula<None>> assumps) {
        this.assumps = assumps;
    }

    @Override
    public int[] solve(final Formula<None> formula, final Abortion aborter) throws AbortionException, SolverException {

        String dimacsOrIscas;
        if (this.tseitin) {
            dimacsOrIscas = FormulaToDimacsConverter.convert(formula, aborter);
            if (AbstractSATChecker.log.isLoggable(Level.FINE)) {
                AbstractSATChecker.log.log(Level.FINE, "CNF length in characters: {0}\n", dimacsOrIscas.length());
                final int nlPos = dimacsOrIscas.indexOf("\n");
                AbstractSATChecker.log.fine("First line of DIMACS problem (# vars, # clauses):\n" + dimacsOrIscas.substring(0, nlPos + 1));
            }
        } else {
            dimacsOrIscas = FormulaToDimacsConverter.convertToIscas(formula, aborter);
            if (AbstractSATChecker.log.isLoggable(Level.FINE)) {
                AbstractSATChecker.log.log(Level.FINE, "ISCAS length in characters: {0}\n", dimacsOrIscas.length());
            }
        }
        return this.solve(dimacsOrIscas, aborter);
    }

    @Override
    public int[] solve(String dimacs, final Abortion aborter) throws AbortionException, SolverException {

        File input = null;
        File output = null;
        File dimacsFromBC2SAT = null;
        try {
            aborter.checkAbortion();
            //    input = File.createTempFile("aproveMiniSAT",".dimacs", curDir);

            input = File.createTempFile("aproveMiniSAT", this.tseitin ? ".dimacs" : ".iscas");
            input.deleteOnExit();
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            //            long time = System.nanoTime();
            inputWriter.write(dimacs);
            //            long diff = System.nanoTime()-time;
            //            System.err.println("Writing MINISAT file ("+(dimacsOrIscas.length()/1024)+"kb) need " + diff + " ns");
            dimacs = null;
            inputWriter.close();
            aborter.checkAbortion();
            //output = File.createTempFile("aproveMiniSAT",".output", curDir);
            output = File.createTempFile("aproveMiniSAT", ".output");
            output.deleteOnExit();

            String args = "";
            if (this.hasAssumps == true) {
                args = "-assumptions ";

                for (final Formula<None> f : this.assumps) {
                    if (f instanceof Variable) {
                        args = args + Integer.toString(f.getId()) + " ";
                    } else if (f instanceof NotFormula) {
                        if (((NotFormula<None>) f).isLiteral()) {
                            args = args + Integer.toString(((NotFormula<None>) f).getLiteralId()) + " ";
                        }
                    }
                }
                args = args + "0 ";
            }

            AbstractSATChecker.log.log(Level.FINER, this.tseitin ? "DIMACS to {0}\n" : "ISCAS to {0}\n", input.getCanonicalPath());
            AbstractSATChecker.log.log(Level.FINER, "OUTPUT to {0}\n", output.getCanonicalPath());

            //ProcessBuilder pb = new ProcessBuilder(COMMAND, input.getCanonicalPath(), output.getCanonicalPath());
            //pb.redirectErrorStream(true);
            //process = pb.start();
            //process = Runtime.getRuntime().exec(COMMAND + " "+input.getCanonicalPath()+" "+output.getCanonicalPath());
            final Socket spawner = ExternalSpawner.getSocket();
            final Writer commandWriter = new OutputStreamWriter(spawner.getOutputStream());
            if (this.tseitin) {
                AbstractSATChecker.log.log(Level.FINER, "Invoking {0}\n", this.COMMAND + args);
                commandWriter.write(this.COMMAND
                    + args
                    + " "
                    + input.getCanonicalPath()
                    + " "
                    + output.getCanonicalPath()
                    + "\n");
            } else {
                dimacsFromBC2SAT = File.createTempFile("aproveMiniSAT", ".dimacs");
                dimacsFromBC2SAT.deleteOnExit();
                final String dimacsPath = dimacsFromBC2SAT.getCanonicalPath();
                final String cmdLine =
                    "bc2sat "
                        + input.getCanonicalPath()
                        + " > "
                        + dimacsPath
                        + " ; "
                        + this.COMMAND
                        + args
                        + " "
                        + dimacsPath
                        + " "
                        + output.getCanonicalPath();
                AbstractSATChecker.log.log(Level.FINER, "DIMACS to {0}\n", dimacsPath);
                AbstractSATChecker.log.log(Level.FINER, "Invoking bc2sat and {0}\n", this.COMMAND + args);
                commandWriter.write(cmdLine + "\n");
            }
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
                AbstractSATChecker.log.log(Level.FINE, "MiniSAT says: {0}\n", result);
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
                if (this.tseitin) {
                    final int[] res = new int[resList.size()];
                    for (int i = 0; i < res.length; i++) {
                        res[i] = resList.get(i);
                    }
                    aborter.checkAbortion();
                    return res;
                } else { // bc2sat assigns new ids, but we need the model for the old ones
                         //  => build map which stores relation
                    final Map<Integer, Integer> newToOld = new HashMap<Integer, Integer>();
                    try (
                        final BufferedReader dimacsCommentReader = new BufferedReader(new FileReader(dimacsFromBC2SAT))) {
                        String line = dimacsCommentReader.readLine();
                        while (line != null && line.startsWith("c")) {
                            if (!line.startsWith("c ***")) { // no meta-comments, please
                                final StringTokenizer st = new StringTokenizer(line);
                                if (Globals.useAssertions) {
                                    assert st.countTokens() == 4;
                                }
                                st.nextToken(); // skip "c"
                                final String newIdString = st.nextToken();
                                st.nextToken(); // skip "="
                                final String iscasGateName = st.nextToken();
                                final char firstChar = iscasGateName.charAt(0);
                                if (firstChar == FormulaToDimacsConverter.iscasGatePrefix) {
                                    // the string to follow firstChar is the old id
                                    final String oldIdString = iscasGateName.substring(1);
                                    final int oldId = Integer.parseInt(oldIdString);
                                    final int newId = Integer.parseInt(newIdString);
                                    newToOld.put(newId, oldId);
                                } else {
                                    if (Globals.useAssertions) {
                                        assert firstChar == FormulaToDimacsConverter.addIscasGatePrefix;
                                    }
                                }
                            }
                            line = dimacsCommentReader.readLine();
                        }
                    }

                    final List<Integer> resListWithOldVars = new ArrayList<Integer>(newToOld.size());
                    final int size = resList.size();
                    for (int i = 0; i < size; i++) {
                        final int resultForNewId = resList.get(i);
                        final Integer oldId = newToOld.get(Math.abs(resultForNewId));
                        if (oldId != null) {
                            // convert result for new vars to result for old vars
                            final Integer resultForOldId = resultForNewId > 0 ? oldId : -oldId;
                            resListWithOldVars.add(resultForOldId);
                        }
                    }
                    final int[] res = new int[resListWithOldVars.size()];
                    for (int i = 0; i < res.length; i++) {
                        res[i] = resListWithOldVars.get(i);
                    }
                    aborter.checkAbortion();
                    return res;
                }
            }
        } catch (final NoSuchElementException e) {
            // just return null
        } catch (final IOException e) {
        } finally {
            if (input != null) {
                input.delete();
            }
            if (dimacsFromBC2SAT != null) {
                dimacsFromBC2SAT.delete();
            }
            if (output != null) {
                output.delete();
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
