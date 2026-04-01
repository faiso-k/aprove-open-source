package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Searches for a solution of polynomial constraints by calling the
 * external tool SICStus Prolog (if available).
 *
 * Does not require any external Java packages. We only require
 * a suitable executable named "sicstus" in the $PATH.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class SicstusPrologFileSearch extends AbstractSearchAlgorithm {

    public enum SicstusMode {
        INTERPRET, // use consult(foo).
        COMPILE, // use compile(foo).
        BOTH // use compile(foo). if this fails due to a representation error
             // (too many permanent variables), use consult(foo) as fallback.
    }

    private static Logger log =
        Logger.getLogger("aprove.verification.oldframework.Algebra.Orders.Utility.POLO.SicstusPrologShellSearch");

    private final SicstusMode mode;

    // introduce extra predicates to keep the clauses short?
    // improves the chances that compiling the clauses works,
    // but extra predicates might be bad for efficiency.
    private final boolean shortClauses;

    // = and >= are to be written like this for the fd solver of sicstus
    private static final String eq = " #= ";
    private static final String ge = " #>= ";

    private static final String tmpPrefix = "aproveSicstus"; // prefix for the temporary prolog program
    public static final String prologVarPrefix = "A";
    // the vars of the prolog program that represent the coefficients
    // are going to have that prefix

    private static final String predicatePrefix = "p";
    //  prefix for the intermediate predicates

    private static final String compileError = "F";
    private static final String noSolution = "N";

    private SicstusPrologFileSearch(final DefaultValueMap<String, BigInteger> ranges, final SicstusMode mode,
            final boolean shortClauses) {
        super(ranges);
        this.mode = mode;
        this.shortClauses = shortClauses;
    }

    public static SicstusPrologFileSearch create(final DefaultValueMap<String, BigInteger> ranges,
        final SicstusMode mode,
        final boolean shortClauses) {
        return new SicstusPrologFileSearch(ranges, mode, shortClauses);
    }

    /**
     * @param var the variable to be turned into a Prolog variable,
     *  it must be possible to make it a Prolog variable simply by
     *  prefixing it with a capital letter
     * @return the Prolog variable that corresponds to var
     */
    public static String toPrologVar(final String var) {
        return SicstusPrologFileSearch.prologVarPrefix + var;
    }

    /**
     * Searches for a solution for the constraints by translating the
     * constraints to SICStus Prolog, asking it for a solution and
     * returning said solution.
     *
     * @param constraints the constraints to solve
     * @param searchStrictConstraints the searchstrict constraints to solve
     * @param aborter the Abortion
     * @return the Map from indefinite coefficients to their numerical value
     *   if such a Map could be found, else null
     */
    @Override
    public Map<String, BigInteger> search(final Set<SimplePolyConstraint> constraints,
        final Set<SimplePolyConstraint> searchStrictConstraints,
        final SimplePolynomial maximizeMe,
        final Abortion aborter) throws AbortionException {
        if (searchStrictConstraints.isEmpty()) {
            return this.actuallySearch(constraints, aborter);
        } else {
            Set<SimplePolyConstraint> candidateConstraints;
            candidateConstraints = new LinkedHashSet<SimplePolyConstraint>(constraints);
            candidateConstraints.addAll(searchStrictConstraints);
            SimplePolyConstraint strictConstraint, prevSPC;
            strictConstraint = null;
            prevSPC = null;
            // make one of the searchstrict constraints strict and try whether
            // a solution is found
            // TODO prolog backtracking
            for (final SimplePolyConstraint spc : searchStrictConstraints) {
                if (strictConstraint != null) { // null => 1st iteration
                    candidateConstraints.remove(strictConstraint);
                    candidateConstraints.add(prevSPC);
                }
                candidateConstraints.remove(spc);
                strictConstraint = new SimplePolyConstraint(spc.getPolynomial(), ConstraintType.GT);
                candidateConstraints.add(strictConstraint);
                Map<String, BigInteger> result;
                result = this.actuallySearch(candidateConstraints, aborter);
                if (result != null) {
                    return result;
                }
                prevSPC = spc;
                aborter.checkAbortion();
            }
            return null;
        }
    }

    private Map<String, BigInteger> actuallySearch(Set<SimplePolyConstraint> constraints, final Abortion aborter)
            throws AbortionException {
        // 1. (a) get the constraint vars
        final SortedSet<String> vars = new TreeSet<String>();
        for (final SimplePolyConstraint c : constraints) {
            vars.addAll(c.getIndefinites());
        }

        // 1. (b) make sure that the variable-dependent ranges are respected
        constraints = new LinkedHashSet<SimplePolyConstraint>(constraints);
        final BigInteger maxRange = super.addRangeConstraints(vars, constraints);

        // 2. convert vars and constraints to sicstus prolog and

        // maps prolog vars to constraint vars
        final String[] prologVars = new String[vars.size()];

        int i = 0; // index for array iteration
        for (final String var : vars) {
            prologVars[i] = SicstusPrologFileSearch.toPrologVar(var);
            // must be done the same way in IndefinitePart.toSicstusProlog
            ++i;
        }

        // Note: Sicstus 3.12.5 says that it cannot cope with clauses whose
        // compiled representation has more than 256 permanent variables. :-(
        // Hence, instead of one big clause, we shall write many small ones.
        // Still leads to trouble for complex interpretations.

        // First, make a list of all variables.
        final StringBuilder varList = new StringBuilder(prologVars.length * 5);
        varList.append("[");
        boolean first = true;
        for (final String var : prologVars) {
            if (!first) {
                varList.append(",");
            }
            varList.append(var);
            first = false;
        }
        varList.append("]");

        // 3. write the prolog program
        final StringBuilder program = new StringBuilder(":- use_module(library(clpfd)).\n");
        program.append("foo(L,T):-L=");
        program.append(varList);
        program.append(", domain(L,0," + maxRange + "),");

        // constraints
        if (this.shortClauses) {
            // with additional predicates
            int count = 0;
            for (final SimplePolyConstraint spc : constraints) {
                ++count;
                program.append(SicstusPrologFileSearch.predicatePrefix);
                program.append(count);
                program.append("(");
                program.append(varList);
                program.append(",T).\n");
                program.append(SicstusPrologFileSearch.predicatePrefix);
                program.append(count);
                program.append("(");
                program.append(varList);
                program.append(",T):- ");
                program.append(spc.getPolynomial().toSicstusProlog());
                switch (spc.getType()) {
                case EQ:
                    program.append(SicstusPrologFileSearch.eq);
                    break;
                case GE:
                    program.append(SicstusPrologFileSearch.ge);
                    break;
                default:
                    throw new RuntimeException("Erroneous constraint type");
                }
                program.append("0,");
            }
        } else {
            // just a single clause
            for (final SimplePolyConstraint spc : constraints) {
                program.append(spc.getPolynomial().toSicstusProlog());
                switch (spc.getType()) {
                case EQ:
                    program.append(SicstusPrologFileSearch.eq);
                    break;
                case GE:
                    program.append(SicstusPrologFileSearch.ge);
                    break;
                default:
                    throw new RuntimeException("Erroneous constraint type");
                }
                program.append("0,");
            }
        }

        program.append("labeling(T,");
        if (this.shortClauses) {
            program.append(varList);
        } else {
            program.append("L");
        }
        program.append(").\n");
        program.append("main:-foo(E,[]),write(E),nl,flush_output,nl.\n");
        program.append("main:-write(\'");
        program.append(SicstusPrologFileSearch.noSolution);
        program.append("\'),nl,flush_output,nl.\n");
        program.append(":-main.\n");

        aborter.checkAbortion();

        // 4. ask Prolog server for a solution
        int[] values;
        SicstusPrologFileSearch.log.log(Level.FINE, "Asking prolog for a solution ...\n");
        values = this.solve(program.toString(), prologVars.length, aborter);
        SicstusPrologFileSearch.log.log(Level.FINE, "Prolog solution search has finished.\n");

        if (values == null) {
            return null;
        }

        // 5. from vars and the list, get the solution that is to be returned
        final Map<String, BigInteger> result = new LinkedHashMap<String, BigInteger>(values.length);
        i = 0;
        for (final String s : vars) { // vars is sorted in the same order as the corresponding values array
            result.put(s, BigInteger.valueOf(values[i]));
            ++i;
        }
        return result;

    }

    /**
     * Have Prolog solve the constraintProblem.
     *
     * @param constraintProblem - to be solved
     * @param numberOfVars - number of different variables in constraintProblem
     * @param aborter
     * @return some corresponding solution values for the variables that
     *  occur in <code>constraintProblem</code> in the order in which they
     *  occur in the initial list of the problem.
     */
    private int[] solve(final String constraintProblem, final int numberOfVars, final Abortion aborter)
            throws AbortionException {
        // write the Prolog constraint problem to a temporary file
        File tmpFile = null;
        String tmpFileName = null;
        try {
            tmpFile = File.createTempFile(SicstusPrologFileSearch.tmpPrefix, ".pl");
            tmpFile.deleteOnExit(); // do not leave a mess
            tmpFileName = tmpFile.getCanonicalPath();
            final OutputStreamWriter wr = new OutputStreamWriter(new FileOutputStream(tmpFile));
            wr.write(constraintProblem);
            wr.close();
        } catch (final IOException e) {
            SicstusPrologFileSearch.log.log(Level.CONFIG, "Writing temporary prolog file " + ((tmpFileName == null) ? "" : (tmpFileName + " "))
                + "has failed, SicstusPrologFileSearch aborted.\n");
            return null;
        }

        if (Globals.useAssertions) {
            assert (tmpFile != null);
        }

        if (SicstusPrologFileSearch.log.isLoggable(Level.FINER)) {
            try {
                SicstusPrologFileSearch.log.log(Level.FINER, "The prolog program has been written to {0}\n", tmpFile.getCanonicalPath());
            } catch (final IOException e) {
                SicstusPrologFileSearch.log.log(Level.FINE, "Getting prolog program path has failed:\n{0}\n", e);
            }
            SicstusPrologFileSearch.log.log(Level.FINEST, "The prolog program looks like this:\n");
            SicstusPrologFileSearch.log.log(Level.FINEST, constraintProblem);
        }
        String answer = this.askSicstus(tmpFile, this.mode, aborter);

        if (Globals.useAssertions) {
            // exactly numberOfVars values
            if (answer != null) {
                if ((!answer.startsWith(SicstusPrologFileSearch.noSolution)) && (!answer.startsWith(SicstusPrologFileSearch.compileError))) {
                    final String[] split = answer.split("\\,");
                    assert split.length == numberOfVars;
                }
            }
        }

        if (answer == null) {
            return null;
        }
        if (this.mode == SicstusMode.BOTH && answer.startsWith(SicstusPrologFileSearch.compileError)) {
            // retry in interpreted mode
            answer = this.askSicstus(tmpFile, SicstusMode.INTERPRET, aborter);
        }

        if (answer.startsWith(SicstusPrologFileSearch.noSolution)) {
            return null; // unsatisfiable over the given range
        }

        if (Globals.useAssertions) {
            assert answer.startsWith("[");
        }

        try (final Scanner sc = new Scanner(answer)) {
        sc.useDelimiter("[\\,\\[\\]]");
            final int[] values = new int[numberOfVars];
            for (int i = 0; i < numberOfVars; ++i) {
                values[i] = sc.nextInt();
            }
            return values;
        }
    }

    private String askSicstus(final File problem, final SicstusMode mode, final Abortion aborter)
            throws AbortionException {
        final Process process;
        try {
            String cmd = null;
            switch (mode) {
            case INTERPRET: {
                cmd = "sicstus --goal consult(\'" + problem.getCanonicalPath() + "\').";
                break;
            }
            default: // COMPILE and BOTH
                cmd = "sicstus --goal compile(\'" + problem.getCanonicalPath() + "\').";
                break;
            }
            if (SicstusPrologFileSearch.log.isLoggable(Level.FINER)) {
                SicstusPrologFileSearch.log.log(Level.FINER, "About to invoke " + cmd + "\n");
            }
            process = Runtime.getRuntime().exec(cmd);
            TrackerFactory.process(aborter, process);
            final BufferedReader stdOut = new BufferedReader(new InputStreamReader(process.getInputStream()));

            final BufferedReader stdErr =
                (mode == SicstusMode.BOTH)
                    ? new BufferedReader(new InputStreamReader(process.getErrorStream()), 262144) : null;

            final String answer = stdOut.readLine();
            if (SicstusPrologFileSearch.log.isLoggable(Level.FINER)) {
                SicstusPrologFileSearch.log.log(Level.FINER, "Sicstus says: {0}\n", answer);
            }
            stdOut.close();
            if (stdErr != null) {
                stdErr.close();
            }

            if (answer == null) {
                process.destroy();
                return SicstusPrologFileSearch.noSolution;
            }

            boolean compileHasFailed = false;
            if (mode == SicstusMode.BOTH) {
                if (answer.startsWith(SicstusPrologFileSearch.noSolution)) {
                    // check whether we did not get a result because of
                    // a Representation error
                    String stdErrLine;
                    while (true) {
                        stdErrLine = stdErr.readLine();
                        if (stdErrLine == null) {
                            break;
                        }
                        if (stdErrLine.startsWith("! Representation error")) {
                            // our constraints are apparently too complex for
                            // compilation.
                            compileHasFailed = true;
                            break;
                        }
                        if (stdErrLine.startsWith("% compiled")) {
                            // apparently no compile error
                            break;
                        }
                    }
                }
                stdErr.close();
            }

            // TODO send EOF instead
            process.destroy();
            if (compileHasFailed) {
                return SicstusPrologFileSearch.compileError;
            } else {
                return answer;
            }
        } catch (final IOException e) {
            SicstusPrologFileSearch.log.log(Level.FINER, "Getting a solution from Prolog has failed:\n" + e);
            return SicstusPrologFileSearch.noSolution;
        }
    }
}
