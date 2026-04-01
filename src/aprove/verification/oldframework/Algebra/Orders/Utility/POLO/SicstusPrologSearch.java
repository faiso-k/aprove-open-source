package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

//import se.sics.jasper.*;


/**
 * Searches for a solution of polynomial constraints by calling
 * the external tool SICStus Prolog (if available).
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class SicstusPrologSearch extends AbstractSearchAlgorithm {

    private static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Orders.Utility.POLO.SicstusPrologSearch");


    private static final String sicstusPackage = "se.sics.jasper.";

    // = and >= are to be written like this for the fd solver of sicstus
    private static final String eq = " #= ";
    private static final String ge = " #>= ";

    private static final String tmpPrefix = "aprove"; // prefix for the temporary prolog program
    private static String sicstusPrefix = "/usr/local/lib/sicstus-3.12.5/"; // where is sicstus? TODO

    private static final String errorMsg = "Could not create Java to Sicstus interface.\n";

    private static final Class[] queryTypes = {String.class, Map.class}; // signature of Prolog.query(...)

    public static final String prologVarPrefix = "A";
    // the vars of the prolog program that represent the coefficients
    // are going to have that prefix

    private static Object prolog = null; // only one server for all queries

    private SicstusPrologSearch(DefaultValueMap<String, BigInteger> ranges) {
        super(ranges);
        SicstusPrologSearch.buildProlog();
    }

    private static synchronized void buildProlog() {
        if (SicstusPrologSearch.prolog == null) {
            try {
                // reflection allows us to include the jasper classes
                // only when really wanted
                Object o = MethodInvoker.invokeStaticMethod(SicstusPrologSearch.sicstusPackage + "Jasper", "newProlog",
                        new Class[]{String.class}, new Object[]{SicstusPrologSearch.sicstusPrefix + "bin/"});
                SicstusPrologSearch.prolog = o;
                //prolog = Jasper.newProlog(sicstusPrefix + "bin/");
            }
            catch (RuntimeException e) {
                throw e;
            }
            catch (Exception e) {
                SicstusPrologSearch.log.log(Level.INFO, SicstusPrologSearch.errorMsg);
            }
        }
    }

    public static SicstusPrologSearch create(DefaultValueMap<String, BigInteger> ranges) {
        return new SicstusPrologSearch(ranges);
    }

    /**
     * @param var the variable to be turned into a Prolog variable,
     *  it must be possible to make it a Prolog variable simply by
     *  prefixing it with a capital letter
     * @return the Prolog variable that correspons to var
     */
    public static String toPrologVar(String var) {
        return SicstusPrologSearch.prologVarPrefix + var;
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
        if (SicstusPrologSearch.prolog == null) {
            SicstusPrologSearch.log.log(Level.INFO, "Interface to Sicstus was not initialized, so no solution could be found.\n");
            return null;
        }
        if (searchStrictConstraints.isEmpty()) {
            return this.actuallySearch(constraints, aborter);
        }
        else {
            Set<SimplePolyConstraint> candidateConstraints;
            candidateConstraints = new LinkedHashSet<SimplePolyConstraint>(constraints);
            candidateConstraints.addAll(searchStrictConstraints);
            SimplePolyConstraint strictConstraint;
            strictConstraint = null;

            // make one of the searchstrict constraints strict and try whether
            // a solution is found
            // TODO prolog backtracking
            for (SimplePolyConstraint spc : searchStrictConstraints) {
                if (strictConstraint != null) { // null => 1st iteration
                    candidateConstraints.remove(strictConstraint);
                }
                candidateConstraints.remove(spc);
                strictConstraint = new SimplePolyConstraint(spc.getPolynomial(), ConstraintType.GT);
                candidateConstraints.add(strictConstraint);
                Map<String, BigInteger> result;
                result = this.actuallySearch(candidateConstraints, aborter);
                if (result != null) {
                    return result;
                }
                aborter.checkAbortion();
            }
            return null;
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

        // 2. convert vars and constraints to sicstus prolog
        // maps prolog vars to constraint vars
        String[] prologVars = new String[vars.size()];
        StringBuilder program = new StringBuilder("library_directory('");
        program.append(SicstusPrologSearch.sicstusPrefix);
        program.append("library').\n:- use_module(library(clpfd)).\n");
        program.append("foo(L,T):-L=");
        int i = 0; // index for array iteration
        for (String var : vars) {
            prologVars[i] = SicstusPrologSearch.toPrologVar(var);
            // must be done the same way in IndefinitePart.toSicstusProlog
            ++i;
        }

        // 3. write the prolog program
        program.append("[");
        boolean first = true;
        for (String var : prologVars) {
            if (!first) {
                program.append(",");
            }
            program.append(var);
            first = false;
        }
        program.append("], domain(L,0," + maxRange + "),");

        // constraints
        for (SimplePolyConstraint spc : constraints) {
            program.append(spc.getPolynomial().toSicstusProlog());
            switch (spc.getType()) {
            case EQ :
                program.append(SicstusPrologSearch.eq);
                break;
            case GE :
                program.append(SicstusPrologSearch.ge);
                break;
            default :
                throw new RuntimeException("Erroneous constraint type");
            }
            program.append("0,\n");
        }

        program.append("labeling(T,L).\n");
        program.append("q(E):-foo(E,[]).\n");

        // 4. ask the prolog "server" for a solution
        int[] values;
        synchronized(SicstusPrologSearch.prolog) {
            //System.out.println("Starting the prolog query");
            values = this.solve(program.toString());
            //System.out.println("Prolog query block ending");
        }

        if (values == null) {
            return null;
        }

        // 5. from vars and the list, get the solution that is to be returned
        Map<String, BigInteger> result = new LinkedHashMap<String, BigInteger>(values.length);
        i = 0;
        for (String s : vars) { // vars is sorted in the same order as the corresponding values array
            result.put(s, BigInteger.valueOf(values[i]));
            ++i;
        }

        return result;
    }

    /**
     * Have Prolog solve the constraintProblem.
     *
     * Only call when you have exclusive access to prolog!
     *
     * @param constraintProblem to be solved
     * @return some corresponding solution values for the variables that
     *  occur in <code>constraintProblem</code> in the order in which they
     *  occur in the initial list of the problem.
     */
    private synchronized int[] solve(String constraintProblem) {
        // first create a file which contains the problem
        File tmpFile = null;
        String fileName = null; // tmp
        try {
            tmpFile = File.createTempFile(SicstusPrologSearch.tmpPrefix, ".pl");
            tmpFile.deleteOnExit(); // do not make a mess
            fileName = tmpFile.getPath();
            FileWriter wr = new FileWriter(fileName);
            wr.write(constraintProblem);
            wr.close();
        }
        catch (IOException e) {
            SicstusPrologSearch.log.log(Level.CONFIG, "Writing temporary prolog query file " +
                    ((fileName == null) ? "" : (fileName+" ")) + "failed, SicstusPrologSearch aborted.\n");
            return null;
        }

        if (Globals.useAssertions) {
            assert(tmpFile != null);
        }

        // consult the actual constraint problem file
        try {
            boolean loadSuccess = (Boolean) MethodInvoker.invokeMethod(SicstusPrologSearch.prolog, "query", SicstusPrologSearch.queryTypes,
                    new Object[]{"consult('"+fileName+"').", null});
            //boolean loadSuccess = prolog.query("consult('"+fileName+"').", null);
            if (! loadSuccess) {
                SicstusPrologSearch.log.log(Level.CONFIG, "Loading the constraint query file " + fileName + " has failed.\n");
                return null;
            }
        }
        //catch (InterruptedException e) {
        //    log.log(Level.CONFIG, "Loading the constraint query file " + fileName + " has failed.\n");
        //    return null;
        //}
        catch (RuntimeException e) {
            throw e;
        }
        catch (Exception e) { // don't throw new Exception(...) in aprove!
            SicstusPrologSearch.log.log(Level.CONFIG, "Exception occurred while loading query file " + fileName + " :\n" + e);
            return null;
        }

        // then get a solution
        Map sicstusMap = new HashMap(2);
        try {
            boolean querySuccess = (Boolean) MethodInvoker.invokeMethod(SicstusPrologSearch.prolog, "query", SicstusPrologSearch.queryTypes,
                    new Object[]{"q(A).", sicstusMap});
            //boolean querySuccess = prolog.query("q(A).", sicstusMap);
            if (! querySuccess) {
                return null;
            }
        }
        catch (RuntimeException e) {
            throw e;
        }
        catch (Exception e) {
            SicstusPrologSearch.log.log(Level.CONFIG,
                    "Unknown Exception occurred while executing query to the given problem.\n" + e);
            return null;
        }
        int[] values = null;
        try {
            Object resultList = sicstusMap.values().iterator().next();
            //Term resultList = (Term) sicstusMap.values().iterator().next();
            Object[] resultArray = (Object[]) MethodInvoker.invokeMethod(resultList, "toPrologTermArray", null, null);
            //Term[] resultArray = resultList.toPrologTermArray();
            values = new int[resultArray.length];
            for (int i = 0; i < values.length; ++i) {
                Long currentValue = (Long) MethodInvoker.invokeMethod(resultArray[i],
                        "getInteger", null, null);
                values[i] = currentValue.intValue();
                //values[i] = (int)resultArray[i].getInteger();
            }
        }
        catch (RuntimeException e) {
            throw e;
        }
        catch (Exception e) {
            SicstusPrologSearch.log.log(Level.CONFIG, "Getting the solution from prolog to aprove has failed.\n" + e);
        }
        return values;
    }
}