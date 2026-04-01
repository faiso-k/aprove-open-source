package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class MiniSATPipeChecker extends AbstractSATChecker {

    private final String COMMAND;

    private final boolean tseitin;

    protected Set<Formula<None>> assumps = new LinkedHashSet<Formula<None>>();
    protected boolean hasAssumps = false;

    public MiniSATPipeChecker(final int version, final boolean simp, final boolean assumps, final boolean tseitin) {
        this.COMMAND = "minisat_proof2stderr";
        this.tseitin = tseitin;
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
            if (AbstractSATChecker.log.isLoggable(Level.FINEST)) {
                AbstractSATChecker.log.log(Level.FINE, "CNF length in characters: {0}\n", dimacsOrIscas.length());
                final int nlPos = dimacsOrIscas.indexOf("\n");
                AbstractSATChecker.log.fine("First line of DIMACS problem (# vars, # clauses):\n" + dimacsOrIscas.substring(0, nlPos + 1));
            }
        } else {
            dimacsOrIscas = FormulaToDimacsConverter.convertToIscas(formula, aborter);
            if (AbstractSATChecker.log.isLoggable(Level.FINEST)) {
                AbstractSATChecker.log.log(Level.FINE, "ISCAS length in characters: {0}\n", dimacsOrIscas.length());
            }
        }
        return this.solve(dimacsOrIscas, aborter);
    }

    @Override
    public int[] solve(final String dimacs, final Abortion aborter) throws AbortionException, SolverException {
        final Process process;
        final File dimacsFromBC2SAT = null;
        Scanner sc = null;
        try {
            aborter.checkAbortion();

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

            //ProcessBuilder pb = new ProcessBuilder(COMMAND, input.getCanonicalPath(), output.getCanonicalPath());
            //pb.redirectErrorStream(true);
            //process = pb.start();
            //process = Runtime.getRuntime().exec(COMMAND + " "+input.getCanonicalPath()+" "+output.getCanonicalPath());
            if (this.tseitin) {
                AbstractSATChecker.log.log(Level.FINER, "Invoking {0}\n", this.COMMAND + args);
                process = Runtime.getRuntime().exec(this.COMMAND + args);
                TrackerFactory.process(aborter, process);
                final Writer writer = new OutputStreamWriter(process.getOutputStream());
                writer.write(dimacs);
                writer.flush();
                writer.close();
            } else {
                throw new UnsupportedOperationException("Not supported. Please use engine 'MINISAT' instead.");
            }
            final BufferedReader stdOut = new BufferedReader(new InputStreamReader(process.getInputStream()));
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
            sc = new Scanner(new InputStreamReader(process.getErrorStream()));
            final String result = sc.next();
            if (!sc.hasNext()) {
                throw new SolverException();
            }
            if (!result.equals("SAT")) {
                if (result.equals("UNSAT")) {
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

            if (this.tseitin) {
                final int[] res = new int[resList.size()];
                for (int i = 0; i < res.length; i++) {
                    res[i] = resList.get(i);
                }
                aborter.checkAbortion();
                return res;
            } else { // bc2sat assigns new ids, but we need the model for the old ones
                     //  => build map which stores relation
                final Map<Integer, Integer> newToOld = new HashMap<>();
                try (final BufferedReader dimacsCommentReader = new BufferedReader(new FileReader(dimacsFromBC2SAT))) {
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
        } catch (final NoSuchElementException e) {
            // just return null
        } catch (final IOException e) {
        } finally {
            if (dimacsFromBC2SAT != null) {
                dimacsFromBC2SAT.delete();
            }
            if (sc != null) {
                sc.close();
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
