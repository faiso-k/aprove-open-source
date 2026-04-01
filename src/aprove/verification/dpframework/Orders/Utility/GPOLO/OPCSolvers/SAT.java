/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * This class is a wrapper for existing SatSearchers. It takes the parameters
 * and provides the configured SatSearcher.
 * @author cotto
 */
public class SAT implements SPCSolver {
    /**
     * In what way is the SPCSimplifier supposed to be invoked on the SPCs?
     */
    private final SimplificationMode simplificationMode;

    /**
     * In what way is the SPCSimplifier supposed to be invoked on the SPCs?
     */
    private final boolean simplifyAll;

    /**
     * In what way is the SPCSimplifier supposed to be invoked on the SPCs?
     */
    private final boolean stripExponents;

    /**
     * This converter transforms SPCs to a SAT problem.
     */
    private final DiophantineSATConverter converter;

    /**
     * This backend solves the SAT problem.
     */
    private final SATCheckerFactory factory;

    /**
     * This constructor is used by the parameter manager.
     */
    @ParamsViaArgumentObject
    public SAT(Arguments arguments) {
        this.converter = arguments.satConverter;
        this.factory = arguments.satBackend;
        this.simplificationMode = arguments.simplification;
        this.simplifyAll = arguments.simplifyAll;
        this.stripExponents = arguments.stripExponents;
    }

    /**
     * Convert and solve the constraints.
     * @param constraints The normal constraints.
     * @param searchStrictConstraints The searchstrict constraints.
     * @param ranges the ranges for the variables
     * @param defaultRange the range for all variables not mentioned in ranges.
     * @param aborter some aborter.
     * @throws AbortionException when the aborter kicks in.
     * @return a value for every variable.
     */
    @Override
    public Map<GPolyVar, BigInteger> search(
            final Set<SimplePolyConstraint> constraints,
            final Set<SimplePolyConstraint> searchStrictConstraints,
            final Map<String, BigInteger> ranges,
            final BigInteger defaultRange,
            final Abortion aborter) throws AbortionException {
        PoloSatConverter poloSatConverter =
            this.converter.getPoloSatConverter(ranges, defaultRange);
        SatSearch satSearcher =
            SatSearch.create(this.factory, poloSatConverter);
        SearchAlgorithm satSearch =
            SimplifyingSearch.create(satSearcher, this.simplifyAll,
                    this.stripExponents, this.simplificationMode);
        Map<String, BigInteger> solution =
            satSearch.search(constraints, searchStrictConstraints, aborter);
        if (solution != null) {
            Map<GPolyVar, BigInteger> result =
                new LinkedHashMap<GPolyVar, BigInteger>();
            for (Map.Entry<String, BigInteger> entry : solution.entrySet()) {
                BigInteger bigInt = entry.getValue();
                result.put(GAtomicVar.createVariable(entry.getKey()), bigInt);
            }
            return result;
        } else {
            return null;
        }
    }

    public static class Arguments {
        /**
         * the backend which solves the SAT problem
         */
        public SATCheckerFactory satBackend;

        /**
         * the converter that transforms the SPCs to a SAT problem.
         */
        public DiophantineSATConverter satConverter;

        /**
         * In which way is the SPCSimplifier supposed to be invoked on the SPCs?
         */
        public SimplificationMode simplification = SimplificationMode.MAXIMUM;
        public boolean simplifyAll = true;
        public boolean stripExponents = false;

    }
}
