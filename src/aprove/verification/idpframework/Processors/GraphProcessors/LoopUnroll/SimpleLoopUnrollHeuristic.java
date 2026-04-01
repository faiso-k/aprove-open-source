package aprove.verification.idpframework.Processors.GraphProcessors.LoopUnroll;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class SimpleLoopUnrollHeuristic implements LoopUnrollHeuristic {

    public static class Arguments {
        public int maxUnrolsPerNode = 1;
    }

    private final int maxUnrolsPerNode;

    @ParamsViaArgumentObject
    public SimpleLoopUnrollHeuristic(final Arguments arguments) {
        this.maxUnrolsPerNode = arguments.maxUnrolsPerNode;
    }

    @Override
    public Set<INode> getUnrolledNodes(final IDPProblem idp,
        final ImmutableMap<INode, IEdge> loopNodes,
        final Abortion aborter) throws AbortionException {
        final ImmutableMap<INode, Integer> nodeUnrollCounter = idp.getIdpGraph().getNodeUnrollCounter();

        final Set<INode> result = new LinkedHashSet<INode>();
        for (final INode node : loopNodes.keySet()) {
            if (nodeUnrollCounter.get(node) < this.maxUnrolsPerNode) {
                result.add(node);
            }
        }

        return result;
    }

}
