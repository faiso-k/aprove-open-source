/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.utility;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.*;
import immutables.*;


public class IdpQUsableRules {

    private ImmutableMap<GeneralizedRule, IActiveCondition> active;

    public IdpQUsableRules (ImmutableMap<GeneralizedRule, IActiveCondition> active) {
        this.active = active;
    }

    public static IdpQUsableRules create(ImmutableMap<GeneralizedRule, IActiveCondition> active) {
        return new IdpQUsableRules(active);
    }

    public ImmutableMap<GeneralizedRule, IActiveCondition> getActive() {
        return this.active;
    }


}
