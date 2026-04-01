package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * A MaxSearchAlgorithm also supports searching for a solution for a
 * Diophantine formula with the side condition that the returned
 * model must satisfy a maximum number of subformulae that are
 * supplied via an additional list.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public interface MaxSearchAlgorithm extends SearchAlgorithm {

    /**
     * Searches for a solution for the given formula.
     * Moreover: the returned model must satisfy a maximum number
     * of subformulae that are supplied via an additional list.
     *
     * @param f
     * @param maxThem
     * @param aborter
     * @return a solution for f (i.e., a model) if such a solution can be found
     *  given the used ranges, moreover the solution will satisfy k elements of
     *  maxThem such that there is no solution for f which satisfies k+1
     *  elements of maxThem; null otherwise
     * @throws AbortionException
     */
    public Map<String, BigInteger> searchMax(Formula<Diophantine> f,
            Collection<Formula<Diophantine>> maxThem, Abortion aborter)
                    throws AbortionException;
}
