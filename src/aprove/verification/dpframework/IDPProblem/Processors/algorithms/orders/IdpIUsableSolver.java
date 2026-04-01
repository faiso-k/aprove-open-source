/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.algorithms.orders;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;

public interface IdpIUsableSolver {

    IActiveOrder solve(IDPProblem idp, IdpQUsableRules usableRules, boolean active, boolean allstrict, Abortion aborter) throws AbortionException;

    IActiveOrder solve(IDPProblem idp, IdpQUsableRules usableRules, Abortion aborter) throws AbortionException;


}
