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
 * external tool CiME (if available).
 *
 * Does not require any external Java packages. We only require
 * a suitable executable named "cime2" in the $PATH.
 *
 * ***************************
 * * CORRECTNESS WARNING     *
 * CiME 2.02 seems to output wrong data once in a while
 * Example:
 * r2.r0 + r5.r3.r0 + r5.r4.r0 + -1.r2.r1
 * + -1.r5.r3.r1 + -1.r2.r4.r1  + -1.r5.r3.r4.r1 + -1.r5.r4.r1  + -1 >= 0
 * and r1 + -1.r0 >= 0
 *
 *
 * @author Patrick Kabasci, based on work by Carsten Fuhs (SicstusPrologFileSearch)
 * @version $Id$
 */
public class CimeFileSearch extends AbstractSearchAlgorithm {

    private static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Orders.Utility.POLO.CimeFileSearch");

    private static long maxVar = 0;

    // = and >= are to be written like this for the fd solver of sicstus
    private static final String eq = " = ";
    private static final String ge = " >= ";
    private static final String gr = " > ";

    private static final String tmpPrefix = "aproveCiME"; // prefix for the name of the temporary CiME file
    public static final String coefficientPrefix = "r"; // must have length 1 and be from [a-zA-Z]

    private static Map<String, Long> varMap = new LinkedHashMap<String, Long>();

    private CimeFileSearch(DefaultValueMap<String, BigInteger> ranges) {
        super(ranges);
    }

    public static CimeFileSearch create(DefaultValueMap<String, BigInteger> ranges) {
        CimeFileSearch.log.log(Level.WARNING, "CORRECTNESS WARNING: You are using the CiME solver. CiME currently seems to have a bug and to output incorrect Data!\n");
        return new CimeFileSearch(ranges);
    }

    /**
     * @param var the variable to be turned into a Prolog variable,
     *  it must be possible to make it a Prolog variable simply by
     *  prefixing it with a capital letter
     * @return the Prolog variable that corresponds to var
     */
    synchronized public static String toVar(String var) {
        long varName;
        if (!CimeFileSearch.varMap.containsKey(var)) {
            CimeFileSearch.varMap.put(var, CimeFileSearch.maxVar++);
            varName = CimeFileSearch.maxVar - 1;
        } else {
            varName = CimeFileSearch.varMap.get(var);
        }
        return CimeFileSearch.coefficientPrefix + Long.toString(varName);
    }
    synchronized public static long toVarInt(String var) {
        long varName;
        if (!CimeFileSearch.varMap.containsKey(var)) {
            CimeFileSearch.varMap.put(var, CimeFileSearch.maxVar++);
            varName = CimeFileSearch.maxVar - 1;
        } else {
            varName = CimeFileSearch.varMap.get(var);
        }
        return varName;
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
    public Map<String, BigInteger> search(Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints, SimplePolynomial maximizeMe, Abortion aborter)
            throws AbortionException {
        if (searchStrictConstraints.isEmpty()) {
            return this.actuallySearch(constraints, aborter);
        }
        else {
            throw new RuntimeException("CimeFileSearch does not support searchstrict mode!");
        }
    }

    private Map<String, BigInteger> actuallySearch(Set<SimplePolyConstraint> constraints,
            Abortion aborter) throws AbortionException {
        // 1. (a) get the constraint vars
        SortedSet<String> vars = new TreeSet<String>();
        for (SimplePolyConstraint c : constraints) {
            vars.addAll(c.getIndefinites());
        }

        // 1. (b) make sure that the variable-dependent ranges are respected
        constraints = new LinkedHashSet<SimplePolyConstraint>(constraints);
        BigInteger maxRange = super.addRangeConstraints(vars, constraints);

        // 2. convert vars and constraints to CiME

        // maps cime vars to constraint vars
        String[] cimeVars = new String[vars.size()];

        int i = 0; // index for array iteration
        for (String var : vars) {
            cimeVars[i] = CimeFileSearch.toVar(var);
            // must be done the same way in IndefinitePart.toCiME
            ++i;
        }



        // 3. write the CiME problem
        StringBuilder program = new StringBuilder("timelimit \"3600000\";\nlet constraints = dioph_constraint \"\n");
        // constraints
        int count = 0;
        for (SimplePolyConstraint spc : constraints) {
            ++count;
            if (count > 1) {
                program.append(" and ");
            }
            program.append(spc.getPolynomial().toCiME());
            switch (spc.getType()) {
            case EQ :
                program.append(CimeFileSearch.eq);
                break;
            case GE :
                program.append(CimeFileSearch.ge);
                break;
            case GT :
                program.append(CimeFileSearch.gr);
                break;
            default :
                throw new RuntimeException("Erroneous constraint type");
            }
            program.append("0");
        }

        program.append("\";");
        program.append("dioph_solve " + maxRange + " constraints;\n");

        aborter.checkAbortion();

        // 4. ask CiME for a solution
        Map<Long, BigInteger> values;
        CimeFileSearch.log.log(Level.FINE, "Asking CiME for a solution ...\n");
        values = this.solve(program.toString(), cimeVars.length, aborter);
        CimeFileSearch.log.log(Level.FINE, "CiME solution search has finished.\n");

        if (values == null) {
            return null;
        }

        // 5. from vars and the list, get the solution that is to be returned
        LinkedHashMap<String, BigInteger> result = new LinkedHashMap<String, BigInteger>(values.size());
        // TODO: Add inverse lookup for Vars as to prevent re-mapping
        for (String s : vars) {
            result.put(s, values.get(CimeFileSearch.toVarInt(s)));
        }
        return result;

    }

    /**
     * Have CiME solve the constraintProblem.
     *
     * @param constraintProblem to be solved
     * @return some corresponding solution values for the variables that
     *  occur in <code>constraintProblem</code> in the order in which they
     *  occur in the initial list of the problem.
     */
    private Map<Long, BigInteger> solve(String constraintProblem, int numberOfVars,
            final Abortion aborter) throws AbortionException {
        // write the CiME constraint problem to a temporary file
        File tmpFile = null;
        String tmpFileName = null;
        try {
            tmpFile = File.createTempFile(CimeFileSearch.tmpPrefix, ".cim2");
            tmpFile.deleteOnExit(); // do not leave a mess
            tmpFileName = tmpFile.getCanonicalPath();
            OutputStreamWriter wr = new OutputStreamWriter(new FileOutputStream(tmpFile));
            wr.write(constraintProblem);
            wr.close();
        }
        catch (IOException e) {
            CimeFileSearch.log.log(Level.CONFIG, "Writing temporary CiME file " +
                    ((tmpFileName == null) ? "" : (tmpFileName+" ")) + "has failed, CiMEFileSearch aborted.\n");
            return null;
        }

        if (Globals.useAssertions) {
            assert(tmpFile != null);
        }

        final Process process;
        try {
            String cmd = "cime2 " + tmpFile.getCanonicalPath();
            if (CimeFileSearch.log.isLoggable(Level.FINER)) {
                CimeFileSearch.log.log(Level.FINER, "The CiME program has been written to {0}\n", tmpFile.getCanonicalPath());
                if (CimeFileSearch.log.isLoggable(Level.FINEST)) {
                    CimeFileSearch.log.log(Level.FINEST, "The CiME program looks like this:\n");
                    CimeFileSearch.log.log(Level.FINEST, constraintProblem);
                }
                CimeFileSearch.log.log(Level.FINER, "About to invoke " + cmd + "\n");
            }
            process = Runtime.getRuntime().exec(cmd);
            BufferedReader stdOut = new BufferedReader(new InputStreamReader(process.getInputStream()));
            TrackerFactory.process(aborter, process);

            List<String> solOutputs = new ArrayList<String>(numberOfVars);
            boolean solExists = false;
            CimeFileSearch.log.finer("CiME says:\n");
            while (true) {
                // assert (this loop terminates eventually);
                // (otherwise CiME does not behave as expected)
                String line = stdOut.readLine();
                if (line == null) {
                    break;
                }
                if (solExists) {
                    if (line.startsWith("-")) { // solution output finished
                        if (CimeFileSearch.log.isLoggable(Level.FINEST)) {
                            CimeFileSearch.log.finest(line + "\n");
                        }
                        break;
                    }
                    else { // the var-to-number assignment
                        solOutputs.add(line);
                        if (CimeFileSearch.log.isLoggable(Level.FINER)) {
                            CimeFileSearch.log.finer(line + "\n");
                        }
                    }
                }
                else if (line.contains("Solution :")) {
                    // From here on, solution values may occur.
                    solExists = true;
                    if (CimeFileSearch.log.isLoggable(Level.FINEST)) {
                        CimeFileSearch.log.finer(line + "\n");
                    }
                }
                else if (line.contains("No solution")) {
                    if (CimeFileSearch.log.isLoggable(Level.FINER)) {
                        CimeFileSearch.log.finer(line + "\n");
                    }
                    break;
                }
                else {
                    // CiME outputs some verbose info,
                    // line only needed for logging
                    if (CimeFileSearch.log.isLoggable(Level.FINEST)) {
                        CimeFileSearch.log.finest(line + "\n");
                    }
                }
            }
            stdOut.close();

            // TODO send EOF instead
            process.destroy();

            if (! solExists) {
                return null;
            }

            Map<Long, BigInteger> values = new LinkedHashMap<Long, BigInteger>(numberOfVars);
            for (String assignment : solOutputs) {
                String[] var = assignment.split("=");
                values.put(Long.parseLong(var[0].trim().substring(1)), BigInteger.valueOf(Long.parseLong(var[1].trim())));
            }

            return values;
        }
        catch (IOException e) {
            CimeFileSearch.log.log(Level.FINER, "Getting a solution from CiME has failed:\n" + e);
            return null;
        }
    }
}
