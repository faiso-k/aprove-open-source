package aprove.verification.dpframework.Heuristics.ReductionPair;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;

/**
 * Use the full subset for search.
 * This heuristic does not really do anything.
 *
 * @author Andreas Kelle-Emden
 */
public class FullSearchHeuristic implements ReductionPairHeuristic{

    @Override
    public Set<Rule> getSubset(QDPProblem qdp) {
        return qdp.getP();
    }

}
