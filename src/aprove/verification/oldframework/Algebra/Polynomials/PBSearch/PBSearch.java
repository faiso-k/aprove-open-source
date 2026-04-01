package aprove.verification.oldframework.Algebra.Polynomials.PBSearch;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Search for a solution by reducing to Pseudo Boolean constraints
 * and using a PB solver.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class PBSearch extends AbstractSearchAlgorithm {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.PBSearch.PBSearch");

    private final PBChecker pbChecker;
    private final boolean fortet;
    private final boolean optimize;

    private PBSearch(DefaultValueMap<String, BigInteger> ranges, PBChecker pbChecker,
            boolean fortet, boolean optimize) {
        super(ranges);
        this.pbChecker = pbChecker;
        this.fortet = fortet;
        this.optimize = optimize;
    }

    /**
     * @param ranges - ranges for the indefinites
     * @param pbChecker - to be used for PB checking
     * @param fortet - true:  use Fortet's linearization<br>
     *                 false: use Glover's linearization
     * @return a new PBSearch
     */
    public static PBSearch create(DefaultValueMap<String, BigInteger> ranges, PBChecker pbChecker,
            boolean fortet, boolean optimize) {
        return new PBSearch(ranges, pbChecker, fortet, optimize);
    }

    /**
     * @param constraints
     * @param searchStrictConstraints
     * @param aborter
     * @throws AbortionException
     */
    @Override
    public Map<String, BigInteger> search(Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints,
            SimplePolynomial maximizeMe, Abortion aborter) throws AbortionException {

        // PBSearch can handle variable-dependent ranges just fine,
        // so no extra code is needed here.

        if (! searchStrictConstraints.isEmpty()) {
            throw new RuntimeException("PBSearch cannot handle Searchstrict mode.\n");
        }

        // we could apply optimization, but we are not supposed to.
        if (! this.optimize) {
            maximizeMe = null;
        }

        SPCToPBConverter converter = SPCToPBConverter.create(this.fortet);
        Quadruple<SimplePolynomial, List<SimplePolyConstraint>, Integer, Map<String, SimplePolynomial>> pb = converter.toPseudoBoolean(constraints,
                maximizeMe, this.ranges, this.ranges.getDefaultValue());


        constraints = null;
        int[] model = this.pbChecker.check(pb.x, pb.w, pb.y, aborter);
        if (model == null) {
            return null;
        }

        Map<String, BigInteger> dioPBInterpretation = new HashMap<String, BigInteger>(model.length - 1);
        final BigInteger ZERO = BigInteger.ZERO;
        final BigInteger ONE = BigInteger.ONE;
        for (int i = 1; i < model.length; ++i) {
            if (model[i] > 0) {
                dioPBInterpretation.put(SPCToPBConverter.PREFIX + i, ONE);
            }
            else {
                dioPBInterpretation.put(SPCToPBConverter.PREFIX + i, ZERO);
            }
        }

        Map<String, BigInteger> result;
        result = new LinkedHashMap<String, BigInteger>(pb.z.size());
        for (Entry<String, SimplePolynomial> e : pb.z.entrySet()) {
            SimplePolynomial sp = e.getValue();
            BigInteger value = sp.interpret(dioPBInterpretation, BigInteger.ZERO);
            result.put(e.getKey(), value);
            if (PBSearch.log.isLoggable(Level.FINEST)) {
                PBSearch.log.log(Level.FINEST, "{0} ", e);
            }
        }
        if (PBSearch.log.isLoggable(Level.FINEST)) {
            PBSearch.log.log(Level.FINEST, "\n");
        }
        return result;
    }
}
