package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A SearchAlgorithm tries to find a solution to Diophantine constraints
 * where only natural numbers are searched for.
 *
 * @author Andreas Capellmann
 * @author Carsten Fuhs
 * @version $Id$
 */
public interface SearchAlgorithm {

    /**
     * @return the mapping from Diophantine variables to their
     *  individual ranges (i.e., the max. values that they may take)
     */
    public DefaultValueMap<String, BigInteger> getRanges();

    /**
     * @param a - a Diophantine variable
     * @return the range (i.e., maximum allowed value)
     *  of the Diophantine variable a
     */
    public BigInteger getRange(String a);

    /**
     * Explicitly sets the range for <code>a</code> to <code>newRange</code>.
     *
     * @param a - a Diophantine variable
     * @param newRange - the new range (i.e., maximum allowed value)
     *  of the Diophantine variable a
     */
    public void putRange(String a, BigInteger newRange);

    /**
     * Searches for a solution for <code>constraints</code> and
     * <code>searchStrictConstraints</code> and returns it as a mapping of the
     * Dio. variables to values by which all of <code>constraints</code> and
     * <code>searchStrictConstraints</code> are satisfied and which orients
     * at least one of <code>searchStrictConstraints</code> strictly if the
     * set is not empty.
     *
     * @param constraints - the SimplePolyConstraints for which a solution is desired
     * @param searchStrictConstraints - is non-empty in SEARCHSTRICT mode:
     *  try to find a solution by which we can order at least one of these
     *  constraints strictly; all elements of searchStrictConstraints must be
     *  of type GE
     * @param maxMe - ignored if null; if non-null, the search alg is asked to try to
     *  find a satisfying valuation that maximizes maxMe
     * @param aborter - the aborter
     * @return a satisfying valuation for the constraints if such a valuation
     *  can be found given the used ranges; null otherwise
     * @throws AbortionException
     */
    public Map<String, BigInteger> search(
            Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints, SimplePolynomial maxMe, Abortion aborter)
            throws AbortionException;

    /**
     * Convenience method which can be implemented e.g. by delegating to
     * search(Set<SimplePolyConstraint>, Set<SimplePolyConstraint>,
     * SimplePolynomial, Abortion) using null as 3rd arg.
     *
     * @see SearchAlgorithm#search(Set, Set, aprove.strategies.Abortions.Abortion)
     * @param constraints
     *            - the SimplePolyConstraints for which a solution is desired
     * @param searchStrictConstraints
     *            - is non-empty in SEARCHSTRICT mode: try to find a solution by
     *            which we can order at least one of these constraints strictly;
     *            all elements of searchStrictConstraints must be of type GE
     * @param aborter
     *            - the aborter
     * @return a satisfying valuation for the constraints if such a valuation
     *         can be found given the used ranges; null otherwise
     * @throws AbortionException
     */
    public Map<String, BigInteger> search(
            Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints, Abortion aborter)
            throws AbortionException;

    /**
     * Searches for a solution for the given formula.
     *
     * @param f
     * @param aborter
     * @return a solution for f (i.e., a model) if such a solution can be found
     *         given the used ranges; null otherwise
     * @throws AbortionException
     */
    public Map<String, BigInteger> search(Formula<Diophantine> f, Abortion aborter)
            throws AbortionException;
    
    /**
     * Searches for a solution for the given formula in linear real arithmetics.
     *
     * @param f
     * @param aborter
     * @return a solution for f (i.e., a model) if such a solution can be found
     *         given the used ranges; null otherwise
     * @throws AbortionException
     */
    public Map<String, BigInteger> searchLRA(Formula<Diophantine> fml, Abortion aborter)
    		throws AbortionException;
    
    /**
     * @return whether search(Formula<Diophantine>, Abortion) is supported
     */
    public boolean supportsDL();

    /**
     * @return the used Diophantine factory (if supported)
     */
    public FormulaFactory<Diophantine> getDLFactory();

    /**
     * @return whether fresh variables are introduced by the algorithm
     *  (whose values should not necessarily be shown to the user)
     */
    public boolean introducesFreshVariables();

	
}
