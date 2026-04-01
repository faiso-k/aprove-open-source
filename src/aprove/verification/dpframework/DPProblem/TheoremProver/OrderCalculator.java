package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Interface for the search for a suitably monotonic order used to strictly
 * orient some rule that is usable for rewriting steps from the rhs of a DP
 * (corresponding monotonicity constraints must be given in the input).
 * Moreover, all rules and pairs of the DP problem are oriented weakly.
 *
 * Here, it is made sure that:
 * If there is an innermost rewriting step with one of the strictly oriented rules
 * from the rhs of the DP, then there is also a rewriting step with this
 * rule at a monotonic position (implying that also the term in the regarded
 * chain actually decreases wrt the order).
 *
 * @author fuhs
 * @author micpar
 * @version $Id$
 */
public interface OrderCalculator {

    /**
     * @param orientThemWeakly - usually the union of R and P from the
     *  input QDP problem, <b>including</b> strictness candidates
     * @param someStrict - at least one of them must be oriented strictly;
     *  the more, the better; which one, does not matter;
     *   all occurring rules must be elements of <code>orientThemWeakly</code>
     * @param strictnessCandidatesDNF - usually combinations of the usable
     *   rules for the "special" DP, candidates for strict orientation;
     *   elements of at least one inner set must all be oriented strictly,
     *   i.e., the param is a flat view of a DNF;
     *   all occurring rules must be elements of <code>orientThemWeakly</code>;
     *   must not be empty (then the result would be "null" anyway,
     *   to find this, one does not need a full-fledged search procedure)
     * @param monConstraintsForFRules - if an f-rule is to be regarded
     *  as oriented strictly for the purpose of the
     *  QDPTheoremProverProcessor, its corresponding monotonicity
     *  constraints must be fulfilled.
     * @param aborter
     * @return a triple with
     *  - x: the non-empty set of strictly oriented rules whose
     *       monotonicity constraints are fulfilled by the order
     *  - y: the monotonicity constraints that are fulfilled by the
     *       order in z
     *  - z: the order used for orienting <code>orientThemWeakly</code>
     *       weakly and at least one of <code>someStrict</code>
     *       strictly (fulfilling its monotonicity constraints at the same
     *       time)
     *  OR null if no such order could be found
     */
    Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder> calculateStrictRulesAndMonotonicity(
            Set<Rule> orientThemWeakly,
            Set<Rule> someStrict,
            Set<Set<Rule>> strictnessCandidatesDNF,
            Map<FunctionSymbol, MonotonicityConstraints> monConstraintsForFRules,
            Abortion aborter) throws AbortionException;


    /**
     *
     * @param orientThemWeakly - usually the union of R and P from the
     *  input QDP problem, except strictness candidates (these are handled
     *  separately)
     * @param strictnessCandidates - usually the usable rules for the
     *  "special" DP, candidates for strict orientation, will also be
     *   oriented weakly
     * @param monConstraintsForFRules - if an f-rule is to be regarded
     *  as oriented strictly for the purpose of the
     *  QDPTheoremProverProcessor, its corresponding monotonicity
     *  constraints must be fulfilled.
     * @param allFRulesStrict - true: require that for some f, all f-rules
     *  in strictnessCandidates are oriented strictly;
     *  false: strict orientation for 1 arbitrary rule suffices
     * @param aborter
     * @return a triple with
     *  - x: the non-empty set of strictly oriented rules whose
     *       monotonicity constraints are fulfilled by the order
     *  - y: the monotonicity constraints that are fulfilled by the
     *       order in z
     *  - z: the order used for orienting <code>orientThemWeakly</code>
     *       weakly and at least one of <code>strictnessCandidates</code>
     *       strictly (fulfilling its monotonicity constraints at the same
     *       time)
     *  OR null if no such order could be found
     */
    @Deprecated
    Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder> calculateStrictRulesAndMonotonicity(
            Set<Rule> orientThemWeakly,
            Set<Rule> strictnessCandidates,
            Map<FunctionSymbol, MonotonicityConstraints> monConstraintsForFRules,
            boolean allFRulesStrict,
            Abortion aborter) throws AbortionException;
}
