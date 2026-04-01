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
public class NonLoopingPathCollapse implements CollapsablePathGenerator {

    @Override
    public CollapsedPathsResult collapsePaths(final TIDPProblem idp,
        final CollapsableEdgesProvider collapsableProvider,
        final float maxEdgeGain,
        final Abortion aborter) throws AbortionException {
        final IDependencyGraph graph = idp.getIdpGraph();
        final List<ImmutableList<IEdge>> collapsedPaths =
            new ArrayList<ImmutableList<IEdge>>();

        final CollectionMap<IEdge, IEdge> splitEdges =
            new CollectionMap<IEdge, IEdge>();

        final EdgeConditionMap newEdgeConditions =
            new EdgeConditionMap(graph.getItpfFactory(), graph.getFreshVarGenerator(), graph.getEdgeConditions());

        final CollectionMap<IFunctionSymbol<?>, INode> newInitialNodes =
            new CollectionMap<IFunctionSymbol<?>, INode>();

        for (final Map.Entry<IFunctionSymbol<?>, ? extends Collection<INode>> nodeEntry : idp.getIdpGraph().getInitialRewriteNodes().entrySet()) {
            newInitialNodes.add(nodeEntry.getKey(), nodeEntry.getValue());
        }

        final Set<IEdge> visitedEdges = new LinkedHashSet<IEdge>();

        final EdgeType colapsedEdgeType = collapsableProvider.getCollapsedEdgeType();
        final Set<ImmutableSet<IEdge>> subGraphs = collapsableProvider.getSubGraphs(idp, aborter);
        final Set<INode> protectedNodes = collapsableProvider.getProtectedNodes(idp, aborter);

        for (final ImmutableSet<IEdge> subGraph : subGraphs) {
            if (Globals.useAssertions) {
                for (final IEdge edge : subGraph) {
                    assert visitedEdges.add(edge) : "apply scc processor before applying NonLoopongInfPathCollapse";
                }
            }

            final LinkedHashSet<IEdge> newScc;
            for (final IEdge startEdge : subGraph) {

                final ArrayList<IEdge> startPath = new ArrayList<IEdge>();
                startPath.add(startEdge);

                final List<ArrayList<IEdge>> result = this.breadthFirstSearch(graph,
                    protectedNodes,
                    startEdge.from,
                    subGraph, colapsedEdgeType,
                    false,
                    Collections.singletonList(startPath));

                if (result != null && (result.size() > 1 || result.get(0).size() > 1)) {
                    newScc = new LinkedHashSet<IEdge>(subGraph);
                    for (final ArrayList<IEdge> path : result) {
                        final IEdge newEdge =
                            this.compactPath(idp,
                                path,
                                splitEdges,
                                colapsedEdgeType,
                                newEdgeConditions,
                                aborter);

                        if (graph.containsInitialRewriteNode(path)) {
                            final ITerm<?> fromTerm = graph.getTerm(newEdge.from);
                            if (fromTerm.isVariable()) {
                                newInitialNodes.add(null, newEdge.from);
                            } else {
                                newInitialNodes.add(((IFunctionApplication<?>) fromTerm).getRootSymbol(),
                                    newEdge.from);
                            }
                        }

                        newScc.remove(path.get(0));
                        newScc.add(newEdge);
                        collapsedPaths.add(ImmutableCreator.create(path));
                    }
                    break;
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
     * adds paths to target not containing loops (exept target -> target)
     * beginning with path fragment to result. If loop is detected, the number
     * of recursions when loop is introduces is returned
     * @param protectedNodes
     * @param colapsedEdgeType
     * @return
     */
    private final List<ArrayList<IEdge>> breadthFirstSearch(final IDependencyGraph graph,
        final Set<INode> protectedNodes, final INode targetNode,
        final ImmutableSet<IEdge> subGraphEdges,
        final EdgeType colapsedEdgeType,
        final boolean allowNonTrivialSubLoops,
        final List<ArrayList<IEdge>> paths) {

        final ArrayList<ArrayList<IEdge>> newQueue = new ArrayList<ArrayList<IEdge>>();

        for (final ArrayList<IEdge> path : paths) {
            final IEdge lastEdge = path.get(path.size() - 1);

            if (lastEdge.to == targetNode || protectedNodes.contains(lastEdge.to)) {
                newQueue.add(path);
                continue;
            }

            final ImmutableMap<INode, ImmutableSet<IEdge>> succNodeEdges =
                graph.getSuccessors(lastEdge.to);

            final List<ArrayList<IEdge>> pathExtensions = new ArrayList<ArrayList<IEdge>>();

            boolean deadEnd = true;
            succLoop : for (final ImmutableSet<IEdge> succEdges : succNodeEdges.values()) {
                for (final IEdge succEdge : succEdges) {
                    if (!succEdge.type.isSubType(colapsedEdgeType)) {
                        if (!succEdge.type.isDisjoint(colapsedEdgeType)) {
                            return null;
                        } else {
                            continue;
                        }
                    }

                    final boolean isLoop = succEdge.to != targetNode && this.checkLoop(path, succEdge);
                    if (isLoop) {
                        if (succEdge.to != succEdge.from && !allowNonTrivialSubLoops) {
                            return null;
                        }
                        deadEnd = true;
                        break succLoop;
                    } else {
                        deadEnd = false;
                        final ArrayList<IEdge> newPath = new ArrayList<IEdge>(path);
                        newPath.add(succEdge);
                        pathExtensions.add(newPath);
                    }
                }
            }

            if (deadEnd) {
                newQueue.add(path);
            } else {
                newQueue.addAll(pathExtensions);
            }
        }

        if (newQueue.equals(paths)) {
            return paths;
        }

        final List<ArrayList<IEdge>> nextLevelResult = this.breadthFirstSearch(graph,
            protectedNodes,
            targetNode,
            subGraphEdges,
            colapsedEdgeType,
            allowNonTrivialSubLoops,
            newQueue);

        return nextLevelResult;
    }

    private boolean checkLoop(final ArrayList<IEdge> path, final IEdge succEdge) {
        if (succEdge.from == succEdge.to) {
            return true;
        }

        for (final IEdge edge : path) {
            if (edge.from == succEdge.to) {
                return true;
            }
        }

        return false;
    }

    /**
     * Introduce new edge and remove old ones
     * @param graph
     * @param path
     * @param newEdgeConditions
     * @param colapsedEdgeType
     * @param aborter
     * @return new edge for compacted path
     * @throws AbortionException
     */
    private IEdge compactPath(final IDPProblem idp,
        final List<IEdge> path,
        final CollectionMap<IEdge, IEdge> splitEdges,
        final EdgeType colapsedEdgeType,
        final EdgeConditionMap newEdgeConditions, final Abortion aborter) throws AbortionException {
        final IDependencyGraph graph = idp.getIdpGraph();
        final FreshVarGenerator freshNames = graph.getFreshVarGenerator();

        final IEdge firstEdge = path.get(0);
        final IEdge lastEdge = path.get(path.size() - 1);
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

        final VariableRenamedPath renamedPath =
            VariableRenamedPath.create(graph, ImmutableCreator.create(ren));

        Itpf pathCondition = graph.itpfPath(renamedPath, PathQuantificationMode.InnerSteps);

        final ItpfSchedulerProof<Itpf, GenericItpfRule<?>> proof = new ItpfSchedulerProof<Itpf, GenericItpfRule<?>>(idp,
                pathCondition,
                idp.getItpfFactory().createTrue());

        ItpfStrategy.HIDDEN_SIMPLIFICATION.getStrategy().apply(proof, ImplicationType.SOUND, aborter);
        pathCondition = graph.getItpfFactory().createAnd(proof.getLastFormulaStates());

        final EdgeType newFirstEdgeType = firstEdge.type.subtractType(colapsedEdgeType);

        newEdgeConditions.putFalse(firstEdge);

        if (newFirstEdgeType != EdgeType.NO_EDGE) {
            final IEdge typeReplacedNewEdge = IEdge.create(firstEdge.from,
                firstEdge.fromPos,
                firstEdge.to,
                newFirstEdgeType);

            newEdgeConditions.putOr(
                typeReplacedNewEdge,
                graph.getCondition(firstEdge));

            splitEdges.add(firstEdge, typeReplacedNewEdge);
        }

        final IEdge newEdge =
            IEdge.create(firstEdge.from, firstEdge.fromPos, lastEdge.to,
                colapsedEdgeType);
        newEdgeConditions.putOr(newEdge, pathCondition);

        splitEdges.add(firstEdge, newEdge);

        return newEdge;
    }

    @Override
    public String getName() {
        return "NonLoopingPathCollapse";
    }

}
