/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.cap.*;
import aprove.verification.dpframework.IDPProblem.utility.*;

public interface IUsableRulesEstimation {

    public static enum Estimations {

        IUSABLERULES_ICAP;

        public static Estimations getDefaultEstimation() {
            return IUSABLERULES_ICAP;
        }

        public static IUsableRulesEstimation getEstimation(IDPRuleAnalysis rules, Estimations estimation) {
            if (estimation == IUSABLERULES_ICAP || estimation == null) {
                return new IUsableRules(rules, new ICap());
            }
            return null;
        }

    }

    /**
     * computes the usable rules for a given set of DPs and
     * the underlying IDPRuleAnalysis (which was passed in the constructor)
     * @param dps
     * @return the set of usable rules, this set may be modified.
     */
    public Set<GeneralizedRule> getUsableRules(Collection<GeneralizedRule> dps);

    public IdpQUsableRules getUsableRules(IDPRuleAnalysis ruleAnalysis);

    public IdpQUsableRules getActiveConditions(TRSTerm t);
}
