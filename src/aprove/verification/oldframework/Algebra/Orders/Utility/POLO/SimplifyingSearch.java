package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Wrapper which allows for conveniently combining the
 * SimplePolyConstraintSimplifier with an arbitrary SearchAlgorithm.
 * That way, the constraints are preprocessed in a first step, and
 * afterwards, the simplified constraints are solved by the embedded
 * SearchAlgorithm.
 *
 * @author fuhs
 * @version $Id$
 */
public class SimplifyingSearch implements SearchAlgorithm {

    private static final Logger log =
        Logger.getLogger("aprove.verification.oldframework.Algebra.Orders.Utility.POLO.SimplifyingSearch");

    // does the actual work after simplification has been performed
    private final SearchAlgorithm searcher;

    // params for simplifier
    private final boolean simplifyAll;
    private final boolean stripExponents;
    private final SimplificationMode mode;

    /**
     * @param searcher - will be used to solve the simplified constraints
     * @param simplifyAll - simplify all constraints (or just non-searchstrict ones?)
     * @param stripExponents - replace a^i by a for i > 1 and range(a) = 1?
     * @param mode - how much simplification is to be performed?
     *  (NONE overrides the other params)
     */
    private SimplifyingSearch(final SearchAlgorithm searcher, final boolean simplifyAll, final boolean stripExponents,
            final SimplificationMode mode) {
        this.searcher = searcher;
        this.simplifyAll = simplifyAll;
        this.stripExponents = stripExponents;
        this.mode = mode;
    }

    /**
     * @param searcher - will be used to solve the simplified constraints
     * @param simplifyAll - simplify all constraints (or just non-searchstrict ones?)
     * @param stripExponents - replace a^i by a for i > 1 and range(a) = 1?
     * @param mode - how much simplification is to be performed?
     *  (NONE overrides the other params)
     */
    public static SimplifyingSearch create(final SearchAlgorithm searcher,
        final boolean simplifyAll,
        final boolean stripExponents,
        final SimplificationMode mode) {
        return new SimplifyingSearch(searcher, simplifyAll, stripExponents, mode);
    }

    @Override
    public Map<String, BigInteger> search(final Set<SimplePolyConstraint> constraints,
        final Set<SimplePolyConstraint> searchStrictConstraints,
        final Abortion aborter) throws AbortionException {
        return this.search(constraints, searchStrictConstraints, null, aborter);
    }

    @Override
    public Map<String, BigInteger> search(final Set<SimplePolyConstraint> constraints,
        final Set<SimplePolyConstraint> searchStrictConstraints,
        SimplePolynomial maximizeMe,
        final Abortion aborter) throws AbortionException {
        Quadruple<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>, Map<String, BigInteger>, Map<String, Set<String>>> constraintsWithMaps;
        // result of simplification

        SimplePolyConstraintSimplifier spcSimplifier;

        long nanos1, nanosTotal;
        nanos1 = System.nanoTime();

        if (this.mode == SimplificationMode.NONE) {
            // do not create a SPCSimplifier if it is not going to be used.
            constraintsWithMaps =
                new Quadruple<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>, Map<String, BigInteger>, Map<String, Set<String>>>(
                    searchStrictConstraints, constraints, Collections.<String, BigInteger>emptyMap(),
                    Collections.<String, Set<String>>emptyMap());
        } else {
            if (SimplifyingSearch.log.isLoggable(Level.FINEST)) {
                SimplifyingSearch.log.log(Level.FINEST, "About to perform polynomial constraint simplification for " + constraints.size()
                    + " normal constraints and " + searchStrictConstraints.size() + " searchstrict constraints.\n");
            }
            spcSimplifier =
                new SimplePolyConstraintSimplifier(constraints, searchStrictConstraints, this.searcher.getRanges(),
                    this.stripExponents);

            constraintsWithMaps = spcSimplifier.simplify(this.mode, this.simplifyAll, aborter);

            // Handle the polynomial which is to be maximized separately.
            if (maximizeMe != null && constraintsWithMaps != null) {
                maximizeMe = SimplifyingSearch.specializePoly(maximizeMe, constraintsWithMaps.y, constraintsWithMaps.z);
            }
        }
        nanosTotal = System.nanoTime() - nanos1;
        if (SimplifyingSearch.log.isLoggable(Level.FINEST)) {
            if (constraintsWithMaps != null) {
                SimplifyingSearch.log.log(Level.FINEST, "Polynomial constraint simplification yielded " + constraintsWithMaps.x.size()
                    + " normal constraints and " + constraintsWithMaps.w.size()
                    + " searchstrict constraints and took {0} ns.\n", nanosTotal);
            } else {
                SimplifyingSearch.log.log(Level.FINEST, "Polynomial constraint simplification took {0} ns.\n", nanosTotal);
            }
        }

        if (constraintsWithMaps == null) {
            if (SimplifyingSearch.log.isLoggable(Level.FINEST)) {
                SimplifyingSearch.log.log(Level.FINEST, "SPCSimplifier has found the constraints to be UNSATISFIABLE for ranges {0}.\n",
                    this.getRanges());
            }
            return null;
        }

        aborter.checkAbortion();

        if (SimplifyingSearch.log.isLoggable(Level.FINEST)) {
            SimplifyingSearch.log.log(Level.FINEST, "About to solve these constraints:\n");
            for (final SimplePolyConstraint spc : constraintsWithMaps.x) {
                SimplifyingSearch.log.log(Level.FINEST, "{0}\n", spc);
            }
            if (!constraintsWithMaps.w.isEmpty()) {
                SimplifyingSearch.log.log(Level.FINEST, "Searchstrict constraints to solve:\n");
                for (final SimplePolyConstraint spc : constraintsWithMaps.w) {
                    SimplifyingSearch.log.log(Level.FINEST, "{0}\n", spc);
                }
            }
        }

        /*
         * solve the remaining constraints and add the information
         * from the maps in order to get a solution
         */
        Map<String, BigInteger> result;

        // first run the search for values on the actual constraints
        // (if there are any)
        if (constraintsWithMaps.x.isEmpty() && constraintsWithMaps.w.isEmpty()) {
            result = new LinkedHashMap<String, BigInteger>();
        } else {
            nanos1 = System.nanoTime();
            result = this.searcher.search(constraintsWithMaps.x, constraintsWithMaps.w, maximizeMe, aborter);
            nanosTotal = System.nanoTime() - nanos1;
            if (SimplifyingSearch.log.isLoggable(Level.FINEST)) {
                final String s = this.searcher.getClass().getSimpleName();
                SimplifyingSearch.log.log(Level.FINEST, s + " took {0} ns.\n", nanosTotal);
            }
        }

        // now add the information from the maps
        if (result != null) {
            result.putAll(constraintsWithMaps.y);
            for (final Entry<String, Set<String>> refEntry : constraintsWithMaps.z.entrySet()) {
                final BigInteger number = result.get(refEntry.getKey());
                if (number != null) {
                    // necessary because of a >= b, b >= a and
                    // a,b in no other constraints
                    // -> a and b take the same value,
                    //    but both indefinites will vanish, so assigning
                    //    a the value of b will not work. Use default value.
                    for (final String indefinite : refEntry.getValue()) {
                        result.put(indefinite, number);
                    }
                }
            }
            if (Globals.useAssertions) {
                final BigInteger defaultValue = BigInteger.ZERO;
                // Has the SimplePolyConstraintSimplifier made any
                // inappropriate transformations?
                for (final SimplePolyConstraint origSPC : constraints) {
                    assert origSPC.interpret(result, defaultValue);
                }

                boolean foundAStrictOne = searchStrictConstraints.isEmpty();
                // if there is no searchstrict constraint to orient,
                // we need not find a strictly oriented one

                for (final SimplePolyConstraint origSPC : searchStrictConstraints) {
                    // check for non-strict orientation ...
                    assert origSPC.interpret(result, defaultValue);

                    // ... and also whether some constraint has been oriented strictly
                    if (!foundAStrictOne) {
                        final SimplePolyConstraint strictSPC =
                            new SimplePolyConstraint(origSPC.getPolynomial(), ConstraintType.GT);
                        if (strictSPC.interpret(result, defaultValue)) {
                            foundAStrictOne = true;
                        }
                    }
                }
                assert foundAStrictOne;
            }
        }
        return result;
    }

    /**
     * @param poly - non-null
     * @param varToNum - non-null (reference and contents)
     * @param newVarToOldVars - non-null (reference and contents)
     * @return the resulting simplified SimplePolynomial
     */
    private static SimplePolynomial specializePoly(final SimplePolynomial poly,
        final Map<String, BigInteger> varToNum,
        final Map<String, Set<String>> newVarToOldVars) {
        final HashMap<String, GENode> subst = new HashMap<String, GENode>();

        // get Var -> number
        for (final Entry<String, BigInteger> vn : varToNum.entrySet()) {
            final GENode numberNode = GENode.create(vn.getValue());
            subst.put(vn.getKey(), numberNode);
        }

        // get oldVar -> newVar
        for (final Entry<String, Set<String>> newToOld : newVarToOldVars.entrySet()) {
            final GENode newVarNode = GENode.create(newToOld.getKey());
            for (final String oldVar : newToOld.getValue()) {
                subst.put(oldVar, newVarNode);
            }
        }
        final SimplePolynomial result = poly.specializeGENode(subst);
        return result;
    }

    @Override
    public Map<String, BigInteger> search(final Formula<Diophantine> f, final Abortion t) throws AbortionException {
        throw new UnsupportedOperationException(
            "SimplePolyConstraintSimplifier cannot deal with arbitrary Diophantine formulae (so far)!");
    }

    @Override
    public DefaultValueMap<String, BigInteger> getRanges() {
        return this.searcher.getRanges();
    }

    @Override
    public BigInteger getRange(final String a) {
        return this.searcher.getRange(a);
    }

    @Override
    public void putRange(final String a, final BigInteger newRange) {
        this.searcher.putRange(a, newRange);
    }

    @Override
    public FormulaFactory<Diophantine> getDLFactory() {
        return this.searcher.getDLFactory();
    }

    @Override
    public boolean supportsDL() {
        return false;
    }

    @Override
    public boolean introducesFreshVariables() {
        return this.searcher.introducesFreshVariables();
    }

	@Override
	public Map<String, BigInteger> searchLRA(Formula<Diophantine> fml, Abortion aborter) throws AbortionException {
		// TODO Auto-generated method stub
		return null;
	}
}
