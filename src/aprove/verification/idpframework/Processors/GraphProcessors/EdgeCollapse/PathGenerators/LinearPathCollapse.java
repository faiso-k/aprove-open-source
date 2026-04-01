package aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.PathGenerators;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.EdgeProviders.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
@Deprecated
public class LinearPathCollapse implements CollapsablePathGenerator {

    @Override
    public CollapsedPathsResult collapsePaths(final TIDPProblem idp,
        final CollapsableEdgesProvider collapsableProvider,
        final float maxEdgeGain,
        final Abortion aborter) throws AbortionException {
        final IDependencyGraph graph = idp.getIdpGraph();

        final List<ImmutableList<IEdge>> collapsedPaths =
            new ArrayList<ImmutableList<IEdge>>();

        final CollectionMap<IFunctionSymbol<?>, INode> newInitialNodes =
            new CollectionMap<IFunctionSymbol<?>, INode>();

        for (final Map.Entry<IFunctionSymbol<?>, ? extends Collection<INode>> nodeEntry : idp.getIdpGraph().getInitialRewriteNodes().entrySet()) {
            newInitialNodes.add(nodeEntry.getKey(), nodeEntry.getValue());
        }

        final CollectionMap<IEdge, IEdge> splitEdges =
            new CollectionMap<IEdge, IEdge>();

        final EdgeConditionMap newEdgeConditions =
            new EdgeConditionMap(idp.getIdpGraph().getItpfFactory(), idp.getIdpGraph().getFreshVarGenerator(), idp.getIdpGraph().getEdgeConditions());

        final EdgeType colapsedEdgeType = collapsableProvider.getCollapsedEdgeType();
        final Set<ImmutableSet<IEdge>> subGraphs = collapsableProvider.getSubGraphs(idp, aborter);
        final Set<INode> protectedNodes = collapsableProvider.getProtectedNodes(idp, aborter);

        for (final ImmutableSet<IEdge> subGraph : subGraphs) {
            final Set<IEdge> remaining =
                new LinkedHashSet<IEdge>(subGraph);

            while (!remaining.isEmpty()) {
                final Iterator<IEdge> iter = remaining.iterator();
                final IEdge edge = iter.next();
                iter.remove();

                // extend path pre
                final LinkedList<IEdge> path = new LinkedList<IEdge>();
                path.add(edge);

                this.extendPre(graph, protectedNodes, colapsedEdgeType, path, remaining);

                // extend path succ
                this.extendSucc(graph, protectedNodes, colapsedEdgeType, path, remaining);

                // replace path
                if (path.size() > 1) {
                    final IEdge newEdge =
                        this.compactPath(idp,
                            path,
                            splitEdges,
                            colapsedEdgeType,
                            newEdgeConditions, aborter);

                    if (graph.containsInitialRewriteNode(path)) {
                        final ITerm<?> fromTerm = graph.getTerm(newEdge.from);
                        if (fromTerm.isVariable()) {
                            newInitialNodes.add(null, newEdge.from);
                        } else {
                            newInitialNodes.add(((IFunctionApplication<?>) fromTerm).getRootSymbol(),
                                newEdge.from);
                        }
                    }

                    collapsedPaths.add(ImmutableCreator.create(path));
                }
            }
        }

        if (!collapsedPaths.isEmpty()) {
            return new CollapsedPathsResult(
                CollectionUtil.immutableCollectionMap(splitEdges),
                ImmutableCreator.create(newEdgeConditions.getMap()));
        } else {
            return null;
        }
    }

    /**
     * @param graph
     * @param protectedNodes
     * @param path
     * @param remaining
     * @param colapsedEdgeType
     * @param currentEdge
     * @return last node visited
     */
    private IEdge extendSucc(final IDependencyGraph graph,
        final Set<INode> protectedNodes,
        final EdgeType colapsedEdgeType,
        final LinkedList<IEdge> path,
        final Set<IEdge> remaining) {

        IEdge currentEdge = path.getLast();

        while (true) {
            if (protectedNodes.contains(currentEdge.to)) {
                break;
            }

            final ImmutableMap<INode, ImmutableSet<IEdge>> succs =
                graph.getSuccessors(currentEdge.to);

            final IEdge uniqueSuccEdge = this.getUniqueEdge(succs, colapsedEdgeType);

            final ImmutableMap<INode, ImmutableSet<IEdge>> pres =
                graph.getSuccessors(currentEdge.to);
            final IEdge uniquePreEdge = this.getUniqueEdge(pres, colapsedEdgeType);

            if (uniqueSuccEdge != null && uniquePreEdge != null && uniquePreEdge.equals(currentEdge)) {
                if (remaining.remove(uniqueSuccEdge)) {
                    path.add(uniqueSuccEdge);
                    currentEdge = uniqueSuccEdge;
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        return currentEdge;
    }

    /**
     * @param graph
     * @param protectedNodes
     * @param currentNode
     * @param path
     * @param remaining
     * @return last node visited
     */
    private IEdge extendPre(final IDependencyGraph graph,
        final Set<INode> protectedNodes,
        final EdgeType colapsedEdgeType,
        final LinkedList<IEdge> path,
        final Set<IEdge> remaining) {

        IEdge currentEdge = path.getFirst();
        while (true) {
            if (protectedNodes.contains(currentEdge.from)) {
                break;
            }

            final ImmutableMap<INode, ImmutableSet<IEdge>> pre =
                graph.getPredecessors(currentEdge.from);

            final IEdge uniquePreEdge = this.getUniqueEdge(pre, colapsedEdgeType);

            final ImmutableMap<INode, ImmutableSet<IEdge>> succs =
                graph.getSuccessors(currentEdge.from);
            final IEdge uniqueSuccEdge = this.getUniqueEdge(succs, colapsedEdgeType);

            if (uniquePreEdge != null && uniqueSuccEdge != null && uniqueSuccEdge.equals(currentEdge)) {
                final IEdge uniquePreSuccEdge = this.getUniqueEdge(graph.getSuccessors(uniquePreEdge.to),
                    colapsedEdgeType);
                if (uniquePreSuccEdge == currentEdge &&
                        remaining.remove(uniquePreEdge)) {
                    path.addFirst(uniquePreEdge);
                    currentEdge = uniquePreEdge;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        return currentEdge;
    }

    private IEdge getUniqueEdge(final Map<INode, ImmutableSet<IEdge>> edges, final EdgeType colapsedEdgeType) {
        IEdge uniqueInfEdge = null;

        for (final Map.Entry<INode, ImmutableSet<IEdge>> edgeEntry : edges.entrySet()) {
            for (final IEdge edge : edgeEntry.getValue()) {
                if (edge.type.isSubType(colapsedEdgeType)) {
                    if (uniqueInfEdge == null && !edge.from.equals(edge.to)) {
                        uniqueInfEdge = edge;
                    } else {
                        return null;
                    }
                } else if (!edge.type.isDisjoint(colapsedEdgeType)){
                    return null;
                }
            }
        }

        return uniqueInfEdge;
    }

    /**
     * Introduce new edge and remove old ones
     * @param graph
     * @param path
     * @param splitEdges
     * @param newEdgeConditions
     * @param colapsedEdgeType
     * @param aborter
     * @return new edge for compacted path
     * @throws AbortionException
     */
    private IEdge compactPath(final IDPProblem idp,
        final LinkedList<IEdge> path,
        final CollectionMap<IEdge, IEdge> splitEdges,
        final EdgeType colapsedEdgeType,
        final EdgeConditionMap newEdgeConditions, final Abortion aborter) throws AbortionException {
        final IDependencyGraph graph = idp.getIdpGraph();
        final FreshVarGenerator freshNames = graph.getFreshVarGenerator();

        final IEdge firstEdge = path.getFirst();
        final IEdge lastEdge = path.getLast();
        final INode firstNode = firstEdge.from;

        final List<ImmutablePair<IEdge, VarRenaming>> ren =
            new ArrayList<ImmutablePair<IEdge, VarRenaming>>(path.size());

        final PolyFactory polyFactory;
        if (idp.getPolyInterpretation() != null) {
            polyFactory = idp.getPolyInterpretation().getFactory();
        } else {
            polyFactory = null;
        }

        for (final IEdge edge : path) {
            if (edge == lastEdge) {
                ren.add(new ImmutablePair<IEdge, VarRenaming>(edge,
                        edge.to == firstNode ? graph.getLoopRenaming(firstNode)
                            : VarRenaming.EMPTY_RENAMING));
            } else {
                final VarRenaming varRenaming = ItpfUtil.getVariableRenaming(polyFactory, graph.getTerm(edge.to).getVariables(), freshNames);
                ren.add(new ImmutablePair<IEdge, VarRenaming>(edge,
                        varRenaming));
            }
        }

        if (Globals.useAssertions) {
            final HashSet<INode> visitedNodes = new HashSet<INode>();
            visitedNodes.add(firstNode);
            for (final IEdge edge : path) {
                assert visitedNodes.add(edge.to) || edge.to == firstNode : "dupplicate node";
            }
        }

        final VariableRenamedPath renamedPath =
            VariableRenamedPath.create(graph, ImmutableCreator.create(ren));

        final Itpf pathCondition = graph.itpfPath(renamedPath, PathQuantificationMode.InnerSteps);

        final ItpfSchedulerProof<Itpf, GenericItpfRule<?>> proof = new ItpfSchedulerProof<Itpf, GenericItpfRule<?>>(idp,
                pathCondition,
                idp.getItpfFactory().createTrue());
        ItpfStrategy.HIDDEN_SIMPLIFICATION.getStrategy().apply(proof, ImplicationType.SOUND, aborter);

        final IEdge newEdge =
            IEdge.create(firstEdge.from, firstEdge.fromPos, lastEdge.to,
                colapsedEdgeType);

        newEdgeConditions.putOr(newEdge,
            graph.getItpfFactory().createAnd(proof.getLastFormulaStates(),
                graph.getFreshVarGenerator()));

        for (final IEdge edge : path) {
            newEdgeConditions.putFalse(edge);
            final IEdge typeSubstractedEdge = IEdge.create(edge.from,
                edge.fromPos,
                edge.to,
                edge.type.subtractType(colapsedEdgeType));

            newEdgeConditions.putOr(
                typeSubstractedEdge,
                graph.getCondition(edge));

            splitEdges.add(edge, typeSubstractedEdge);
            splitEdges.add(edge, newEdge);
        }

        return newEdge;
    }

    @Override
    public String getName() {
        return "LinearPathCollapse";
    }

}
