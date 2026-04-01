package aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.PathGenerators;

import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class CollapsedPathsResult implements Immutable {

    public final ImmutableMap<IEdge, ImmutableSet<IEdge>> edgeSplit;
    public final ImmutableMap<IEdge, Itpf> newEdgeConditions;

    public CollapsedPathsResult(final ImmutableMap<IEdge, ImmutableSet<IEdge>> edgeSplit,
            final ImmutableMap<IEdge, Itpf> newEdgeConditions) {
        this.edgeSplit = edgeSplit;
        this.newEdgeConditions = newEdgeConditions;
    }

}
