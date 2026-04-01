package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Abstract superclass to facilitate implementation of the interface
 * SearchAlgorithm.
 *
 * @see SearchAlgorithm
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class AbstractSearchAlgorithm implements SearchAlgorithm {

    protected DefaultValueMap<String, BigInteger> ranges;

    protected AbstractSearchAlgorithm(final DefaultValueMap<String, BigInteger> ranges) {
        this.ranges = ranges;
    }

    @Override
    public BigInteger getRange(final String a) {
        return this.ranges.get(a);
    }

    @Override
    public DefaultValueMap<String, BigInteger> getRanges() {
        return this.ranges;
    }

    @Override
    public void putRange(final String a, final BigInteger newRange) {
        this.ranges.put(a, newRange);
    }

    // default implementation for convenience
    @Override
    public Map<String, BigInteger> search(final Set<SimplePolyConstraint> constraints,
        final Set<SimplePolyConstraint> searchStrictConstraints,
        final Abortion aborter) throws AbortionException {
        return this.search(constraints, searchStrictConstraints, null, aborter);
    }

    // default implementation, override where sensible
    @Override
    public Map<String, BigInteger> search(final Formula<Diophantine> f, final Abortion t) throws AbortionException {
        throw new UnsupportedOperationException(
            "As of now, this SearchAlgorithm does not support searching for solutions for Diophantine Formulae!");
    }
    
	public Map<String, BigInteger> searchLRA(final Formula<Diophantine> f, final Abortion aborter) throws AbortionException {
		// TODO Auto-generated method stub
		 throw new UnsupportedOperationException(
		            "As of now, this SearchAlgorithm does not support searching for solutions for linear real arithemtics for Diophantine Formulae!");
	}

    /**
     * Adds constraints to <code>constraints</code> that make sure that
     * the individual ranges of the Diophantine variables in
     * <code>dioVars</code> are not exceeded even if the underlying
     * search backend does not support variable-dependent ranges.
     *
     * Helper method for implementors. Useful if the search backend only
     * supports a fixed range for /all/ Diophantine variables.
     *
     * @param dioVars - we need constraints to limit the range for these
     * @param constraints - additional constraints are added here
     * @return the range that should be used for the search backend
     *  (i.e., the maximum range for the Diophantine variables in dioVars)
     */
    protected BigInteger addRangeConstraints(final Collection<SimplePolyConstraint> constraints,
        final Collection<SimplePolyConstraint> searchStrictConstraints) {
        final Set<String> vars = new LinkedHashSet<String>();
        for (final SimplePolyConstraint c : constraints) {
            vars.addAll(c.getIndefinites());
        }
        for (final SimplePolyConstraint c : searchStrictConstraints) {
            vars.addAll(c.getIndefinites());
        }

        final BigInteger result = this.addRangeConstraints(vars, constraints);
        return result;
    }

    /**
     * Adds constraints to <code>constraints</code> that make sure that
     * the individual ranges of the Diophantine variables in
     * <code>dioVars</code> are not exceeded even if the underlying
     * search backend does not support variable-dependent ranges.
     *
     * Helper method for implementors. Useful if the search backend only
     * supports a fixed range for /all/ Diophantine variables.
     *
     * @param dioVars - we need constraints to limit the range for these
     * @param constraints - additional constraints are added here
     * @return the range that should be used for the search backend
     *  (i.e., the maximum range for the Diophantine variables in dioVars)
     */
    protected BigInteger addRangeConstraints(final Set<String> dioVars,
        final Collection<SimplePolyConstraint> constraints) {
        final BigInteger maxRange = this.getMaxRange(dioVars);
        for (final String a : dioVars) {
            final BigInteger range = this.getRange(a);
            if (range.compareTo(maxRange) < 0) {
                // we need a constraint to restrict the range for this one
                final SimplePolynomial poly = SimplePolynomial.create(range).minus(SimplePolynomial.create(a));
                final SimplePolyConstraint spc = new SimplePolyConstraint(poly, ConstraintType.GE);
                constraints.add(spc);
            }
        }
        return maxRange;
    }

    private BigInteger getMaxRange(final Set<String> dioVars) {
        BigInteger result = BigInteger.ZERO;
        for (final String a : dioVars) {
            final BigInteger r = this.getRange(a);
            if (r.compareTo(result) > 0) {
                result = r;
            }
        }
        return result;
    }

    // default implementation, override where sensible
    @Override
    public boolean supportsDL() {
        return false;
    }

    // default implementation, override where sensible
    @Override
    public FormulaFactory<Diophantine> getDLFactory() {
        return null;
    }

    // default implementation, override where sensible
    @Override
    public boolean introducesFreshVariables() {
        return false;
    }


}
