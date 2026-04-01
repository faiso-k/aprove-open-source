package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

/**
 * Heuristic to determine a DNF representation of which rules
 * to try to orient strictly for QDPTheoremProverProcessor.
 *
 * @author fuhs
 */
public interface RuleCandidateHeuristic {

    /**
     *
     * @param protoCandidates - pick candidates from this set
     * @param dpRhs - the rhs of the DP from which we start
     * @param forbiddenCandidates - will not be includes in the result
     * @return a DNF stating which rules must be oriented strictly
     *  (and suitably monotonically) by the SAT solver
     */
    Set<Set<Rule>> selectCandidatesAsDNF(ImmutableSet<Rule> protoCandidates,
            TRSFunctionApplication dpRhs, Set<Rule> forbiddenCandidates);
}
