package aprove.verification.complexity.CIdtProblem.Utility;

import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class CIdtCollapsedPathsResult {
    public final ImmutableMap<Pair<IEdge, IEdge>, ImmutableSet<IEdge>> edgeSplit;
    public final ImmutableMap<IEdge, Itpf> newEdgeConditions;
    public final ImmutableSet<IEdge> newK;
    public final ImmutableSet<IEdge> newS;
    public final ImmutableMap<IEdge, Integer> collapsedSelfLoops;

    public CIdtCollapsedPathsResult(
            final ImmutableMap<Pair<IEdge, IEdge>, ImmutableSet<IEdge>> edgeSplit,
            final ImmutableMap<IEdge, Itpf> newEdgeConditions,
            ImmutableSet<IEdge> newS, ImmutableSet<IEdge> newK, ImmutableMap<IEdge, Integer> collapsedSelfLoops) {

        this.edgeSplit = edgeSplit;
        this.newEdgeConditions = newEdgeConditions;
        this.newS = newS;
        this.newK = newK;
        this.collapsedSelfLoops = collapsedSelfLoops;
    }
}
