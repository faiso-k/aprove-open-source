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
 * AProVE (the termination prover which generates Diophantine problems)
 *  feat.
 * AProVE (the stand-alone Diophantine solver)!
 *
 * Note that the Diophantine server backend must be invoked with the
 * maximal range that is allowed for some Diophantine variable
 * (variable-dependent ranges are not supported by the backend interface
 * so far).
 *
 * Disclaimer: Unless your aim is to investigate the overhead induced
 * by using AProVE as an /external/ constraint solving back-end in
 * server mode, you may wish to consider using a different SearchAlgorithm
 * to solve your constraints.
 *
 * @author Karsten Behrmann
 * @author Carsten Fuhs
 * @version $Id$
 */
public class AProVESearch extends AbstractSearchAlgorithm {

    private final static Pattern solutionMatcher = Pattern.compile("^\\+ ([^=]+) = ([0-9]+)$");

    private final static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Orders.Utility.POLO.AProVESearch");

    private final String inFIFO;
    private final String outFIFO;
    private static final Checker<Map<String, BigInteger>> theChecker = new DioAProVEFileChecker();
    private static final PolyFormatter theFormatter = PolyFormatter.RATSOLVER;

    private AProVESearch(DefaultValueMap<String, BigInteger> ranges,
            String inFIFO, String outFIFO) {
        super(ranges);
        this.inFIFO = inFIFO;
        this.outFIFO = outFIFO;
    }

    public static SearchAlgorithm create(DefaultValueMap<String, BigInteger> ranges,
            String inFIFO, String outFIFO) {
        return new AProVESearch(ranges, inFIFO, outFIFO);
    }

    /**
     * There can be only one searching thread at a time.
     */
    @Override
    public synchronized Map<String, BigInteger> search(Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints, SimplePolynomial maximizeMe, Abortion abortion)
            throws AbortionException {
        if (! searchStrictConstraints.isEmpty()) {
            throw new RuntimeException("AProVESearch does not support searchstrict mode!");
        }

        // make sure that the variable-dependent ranges are respected
        Set<SimplePolyConstraint> constraintsCopy = new LinkedHashSet<SimplePolyConstraint>(constraints);
        BigInteger maxRange = super.addRangeConstraints(constraintsCopy,
                Collections.<SimplePolyConstraint>emptySet());

        String problem = this.constraintsToString(constraintsCopy, abortion) + "\n#\n";

        return FileCheckerHelper.checkWithGivenFiles(problem, abortion,
                AProVESearch.theChecker, this.inFIFO, this.outFIFO);
    }

    private String constraintsToString(Set<SimplePolyConstraint> constraints, Abortion abortion) throws AbortionException {
        StringBuilder buffer = new StringBuilder();
        boolean inString = false;
        for(SimplePolyConstraint constraint: constraints) {
            if (inString) {
                buffer.append(";\n");
            }
            else {
                inString = true;
            }
            buffer.append(constraint.toStringRep(AProVESearch.theFormatter));
        }
        return buffer.toString();
    }

    /**
     *  Local helper class.
     */
    private static class DioAProVEFileChecker implements Checker<Map<String, BigInteger>> {
        @Override
        public Map<String, BigInteger> readResult(BufferedReader resultReader) throws IOException {
            String line;
            line = resultReader.readLine();

            // while .hotspot_compiler leads to output to stdout, just ignore it
            while (line.startsWith("CompilerOracle") || line.startsWith("###")) {
                line = resultReader.readLine();
            }

            if (AProVESearch.log.isLoggable(Level.FINEST)) {
                AProVESearch.log.finest("Dio-AProVE sez: " + line + "\n");
            }

            if (! "+SOLUTION:".equals(line)) {
                resultReader.readLine(); // read the "#"
                return null;
            }

            Map<String, BigInteger> solution = new LinkedHashMap<String, BigInteger>();
            while(! (line=resultReader.readLine()).equals("#")) {
                if (line.startsWith("###")) { // CompilerOracle
                    break;
                }
                if (AProVESearch.log.isLoggable(Level.FINEST)) {
                    AProVESearch.log.finest("Dio-AProVE sez: " + line + "\n");
                }
                if (line.equals("-")) {
                    resultReader.readLine(); // read the "#"
                    break; // End of output
                }
                Matcher match = AProVESearch.solutionMatcher.matcher(line);
                if (! match.matches()) {
                    AProVESearch.log.warning("Unexpected line from external Diophantine solver AProVE: " + line + "\n");
                    continue;
                }
                solution.put(match.group(1), BigInteger.valueOf(Long.parseLong(match.group(2))));
            }
            return solution;
        }
    }
}
