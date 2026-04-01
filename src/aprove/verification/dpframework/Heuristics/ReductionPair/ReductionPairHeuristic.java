package aprove.verification.dpframework.Heuristics.ReductionPair;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;

/**
 * Interface for reduction pair heuristics.
 * Given a qdp problem these heuristics calculate which
 * pairs should be regarded for strictness.
 *
 * The subset will either be oriented strictly (allstrict = true)
 * or the reduction pair processor will search for at least one strictly
 * oriented pair in this subset.
 *
 * @author Andreas Kelle-Emden
 */
public interface ReductionPairHeuristic {

    /**
     * Execute the heuristic and calculate the subset
     *
     * @param qdp The qdp
     * @return Subset of P
     */
    Set<Rule> getSubset(QDPProblem qdp);
}
