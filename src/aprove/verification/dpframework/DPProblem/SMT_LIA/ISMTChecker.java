/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.SMT_LIA;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Provides an satisfiability test (SMT) of formulas over QF_LIA logic
 * (quantifier free linear integer arithmetic).
 *
 * Linear integer arithmetic allows for relations between linear polynomials.
 *
 * @author noschinski
 */
public interface ISMTChecker {

    /**
     * Checks if formula is satisfiable.
     *
     * @formula Formula to check. All polynomials must be linear.
     * @aborter Aborts the test if it is taking too long.
     *
     * @return Returns YNM.Maybe iff the satisfiability could not be decided
     *     or an error occured.
     */
    public YNM isSatisfiable(ImmutableBoolOp<LIAConstraint> formula, Abortion aborter) throws AbortionException;

}
