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
public interface CollapsableEdgesProvider {

    public Set<ImmutableSet<IEdge>> getSubGraphs(final TIDPProblem idp, Abortion aborter) throws AbortionException;

    /**
     * @return nodes which may only occur at beginning / end of compacted path
     */
    public Set<INode> getProtectedNodes(final TIDPProblem idp, Abortion aborter) throws AbortionException;

    public EdgeType getCollapsedEdgeType();

    public String getName();
}
