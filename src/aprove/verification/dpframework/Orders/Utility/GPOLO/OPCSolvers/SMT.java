package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class is a wrapper for existing SmtSearchers. It takes the parameters
 * and provides the configured SmtSearcher.
 * @author Ckuknat
 */
public class SMT implements SPCSolver {

    /**
     * This backend solves the SMT problem.
     */
    private final SMTEngine factory;

    /**
     * This constructor is used by the parameter manager.
     */
    @ParamsViaArgumentObject
    public SMT(final Arguments arguments) {
        this.factory = arguments.smtBackend;
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
    public Map<GPolyVar, BigInteger> search(final Set<SimplePolyConstraint> constraints,
        final Set<SimplePolyConstraint> searchStrictConstraints,
        final Map<String, BigInteger> ranges,
        final BigInteger defaultRange,
        final Abortion aborter) throws AbortionException {

        assert (defaultRange != null && ranges != null);
        DefaultValueMap<String, BigInteger> defaultRanges;
        defaultRanges = new DefaultValueMap<String, BigInteger>(defaultRange);
        defaultRanges.putAll(ranges);
        SearchAlgorithm smtSearch;
        smtSearch = this.factory.getSearchAlgorithm(defaultRanges);
        final Map<String, BigInteger> solution = smtSearch.search(constraints, searchStrictConstraints, aborter);
        if (solution != null) {
            final Map<GPolyVar, BigInteger> result = new LinkedHashMap<GPolyVar, BigInteger>();
            for (final Map.Entry<String, BigInteger> entry : solution.entrySet()) {
                final BigInteger bigInt = entry.getValue();
                result.put(GAtomicVar.createVariable(entry.getKey()), bigInt);
            }
            return result;
        } else {
            return null;
        }
    }

    public static class Arguments {
        /**
         * the backend which solves the SMT problem
         */
        public SMTEngine smtBackend = null;
    }

}
