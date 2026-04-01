package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.logging.*;
import java.util.regex.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.ExternalProcess.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * POLO-Solving a la Spain
 *
 * @author Karsten Behrmann
 * @version $Id$
 */
public class MultiSolverFileSearch extends AbstractSearchAlgorithm implements StdoutChecker<Map<String, BigInteger>> {

    public enum Backend {
        VALENCIA, BARCELONA;
    }

    private final static String VALENCIA_PROG = "MultiSolver";
    private final static String VALENCIA_TIMEOUT = "315360000"; // 10 years (without any Feb 29th)
    private final static String BARCELONA_PROG = "barcelona";
    private final static PolyFormatter FORMATTER = PolyFormatter.MULTISOLVER;

    private final Backend backend;

    private final static Pattern solutionMatcher = Pattern.compile("^\\+\\s+([^\\s=]+)\\s*=\\s*([0-9]+)\\s*$");

    private final static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Orders.Utility.POLO.MultiSolverFileSearch");

    private MultiSolverFileSearch(DefaultValueMap<String, BigInteger> ranges, Backend backend) {
        super(ranges);
        this.backend = backend;
    }

    public static SearchAlgorithm create(DefaultValueMap<String, BigInteger> ranges,
            Backend t) {
        return new MultiSolverFileSearch(ranges, t);
    }

    @Override
    public String getTempPrefix() {
        return "constraints";
    }

    @Override
    public String getInputTempSuffix() {
        return "polo";
    }

    @Override
    public Map<String, BigInteger> search(Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints, SimplePolynomial maximizeMe, Abortion abortion)
            throws AbortionException {
        if (! searchStrictConstraints.isEmpty()) {
            throw new RuntimeException("MultiSolverFileSearch does not support searchstrict mode!");
        }

        // make sure that the variable-dependent ranges are respected
        Set<SimplePolyConstraint> constraintsCopy = new LinkedHashSet<SimplePolyConstraint>(constraints);
        BigInteger maxRange = super.addRangeConstraints(constraintsCopy,
                Collections.<SimplePolyConstraint>emptySet());

        String problem = this.constraintsToString(constraintsCopy, abortion);
        if (this.backend == Backend.VALENCIA) {
            return FileCheckerHelper.checkWithStdout(problem, abortion, this,
                    MultiSolverFileSearch.VALENCIA_PROG, "-m", MultiSolverFileSearch.VALENCIA_TIMEOUT, "-d", "N" + maxRange, "-t", "SAT");
                    // TODO technique should not be fixed
        } else if (this.backend == Backend.BARCELONA) {
            return FileCheckerHelper.checkWithStdout(problem, abortion, this,
                    MultiSolverFileSearch.BARCELONA_PROG, maxRange.toString());
        } else {
            throw new IllegalArgumentException("Bad technique in MultiSolver");
        }
    }

    private String constraintsToString(Set<SimplePolyConstraint> constraints, Abortion abortion) {
        StringBuilder buffer = new StringBuilder();
        boolean inString = false;
        for(SimplePolyConstraint constraint: constraints) {
            if (inString) {
                buffer.append(";\n");
            }
            else {
                inString = true;
            }
            buffer.append(constraint.toStringRep(MultiSolverFileSearch.FORMATTER));
        }
        return buffer.toString();
    }

    @Override
    public Map<String, BigInteger> readResult(BufferedReader result) throws IOException {
        String line;
        line = result.readLine();
        if (MultiSolverFileSearch.log.isLoggable(Level.FINEST)) {
            MultiSolverFileSearch.log.finest("result from MultiSolver: " + line);
        }
        if (line == null || !"+SOLUTION:".equals(line.trim())) {
            return null;
        }

        Map<String, BigInteger> solution = new LinkedHashMap<String, BigInteger>();
        while( (line=result.readLine()) != null) {
            if (MultiSolverFileSearch.log.isLoggable(Level.FINEST)) {
                MultiSolverFileSearch.log.finest("multisolver sez: " + line);
            }
            if (line.equals("-")) {
                break; // End of output
            }
            Matcher match = MultiSolverFileSearch.solutionMatcher.matcher(line);
            if (! match.matches()) {
                MultiSolverFileSearch.log.warning("Unexpected line from MultiSolver: " + line);
                continue;
            }
            solution.put(match.group(1), BigInteger.valueOf(Long.parseLong(match.group(2))));
        }
        return solution;
    }
}
