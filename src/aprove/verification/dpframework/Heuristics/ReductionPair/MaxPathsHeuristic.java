package aprove.verification.dpframework.Heuristics.ReductionPair;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Calculate for every pair the number of paths through the corresponding node in the DP graph.
 * Then only the pair with the maximal value is regarded further.
 *
 * @author Andreas Kelle-Emden
 */
public class MaxPathsHeuristic implements ReductionPairHeuristic{

    @Override
    public Set<Rule> getSubset(QDPProblem qdp) {

        Graph<Rule, ?> graph = qdp.getDependencyGraph().getGraph();
        Set<Node<Rule>> nodeSet = graph.getNodes();

        int paths = 0;
        Rule p = null;
        for (Node<Rule> node : nodeSet) {
            int newPaths = graph.getIn(node).size() * graph.getOut(node).size();
            if (newPaths > paths) {
                paths = newPaths;
                p = node.getObject();
            }
        }

        if (p == null) {
            // We have either no pairs or no connections between the pairs
            // Anyway the system is trivial (but not with the reduction pairs processor)
            return null;
        }

        LinkedHashSet<Rule> res = new LinkedHashSet<Rule>(1);
        res.add(p);

        return res;
    }

}
