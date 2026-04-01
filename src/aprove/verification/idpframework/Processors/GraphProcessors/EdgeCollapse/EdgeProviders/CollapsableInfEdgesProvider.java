package aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.EdgeProviders;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class CollapsableInfEdgesProvider implements CollapsableEdgesProvider {

    @Override
    public Set<ImmutableSet<IEdge>> getSubGraphs(final TIDPProblem idp, final Abortion aborter) {
        final Set<ImmutableSet<IEdge>> res = new LinkedHashSet<ImmutableSet<IEdge>>();

        for (final IDPSubGraph subGraph : idp.getSubGraphs()) {
            res.add(subGraph.getEdges());
        }

        return res;
    }

    @Override
    public EdgeType getCollapsedEdgeType() {
        return EdgeType.INF;
    }

    @Override
    public Set<INode> getProtectedNodes(final TIDPProblem idp, final Abortion aborter)
            throws AbortionException {
        return Collections.emptySet();
    }

    @Override
    public String getName() {
        return "CollapsableInfEdgesProvider";
    }



}
