/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Algorithms.UsableRules;

import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Polynomials.*;

public interface IUsableRulesEstimation {

    public static enum Estimations {

        IUSABLERULES_ICAP;

        public static Estimations getDefaultEstimation() {
            return IUSABLERULES_ICAP;
        }

        public static IUsableRulesEstimation getEstimation(final Estimations estimation) {
            if (estimation == IUSABLERULES_ICAP || estimation == null) {
                return new UnconditionalUsableRules();
            }
            return null;
        }

    }

    /**
     * computes the usable rules for a given node under a certain substitution
     * and precondition in the underlying IDependencyGraph
     * @param relDependency
     * @param
     * @return the set of usable rules, this set may be modified.
     */
    public IDPUsableRulesResult getUsableRules(IDPProblem idp,
        Itpf precondition,
        RelDependency relDependency,
        INode node,
        ImmutablePolyTermSubstitution substitution);

    /**
     * computes the usable rules for a given term a certain substitution
     * and precondition in the underlying IDependencyGraph
     * @param
     * @return the set of usable rules, this set may be modified.
     */
    public IDPUsableRulesResult getUsableRules(IDPProblem idp,
        Itpf precondition,
        RelDependency relDependency,
        IActiveCondition activeCOndition,
        ITerm<?> term);


    public IDPUsableRulesResult getUsableRules(IDPProblem idp,
        Itpf precondition,
        RelDependency relationalDependency,
        IActiveCondition activeCondition,
        IEdge edge,
        ImmutablePolyTermSubstitution substitution);

}
