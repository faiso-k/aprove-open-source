package aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.PathGenerators;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.EdgeProviders.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class NodeCollapsingPathGenerator implements CollapsablePathGenerator {

    @Override
    public CollapsedPathsResult collapsePaths(final TIDPProblem idp,
        final CollapsableEdgesProvider collapsableProvider,
        final float maxEdgeGain,
        final Abortion aborter) throws AbortionException {
        final Set<ImmutableSet<IEdge>> subGraphs = collapsableProvider.getSubGraphs(idp, aborter);
        final Set<INode> protectedNodes = collapsableProvider.getProtectedNodes(idp, aborter);
        final EdgeType collapsedEdgeType = collapsableProvider.getCollapsedEdgeType();

        final IDependencyGraph graph = idp.getIdpGraph();
        final ImmutableSet<IEdge> originalEdges = graph.getEdges();

        final EdgeConditionMap newEdgeConditions =
            new EdgeConditionMap(graph.getItpfFactory(), graph.getFreshVarGenerator(), graph.getEdgeConditions());

        final ImmutableMap<INode, ? extends ITerm<?>> nodeTerms = graph.getNodeMap();

        final DoubleKeyCollectionMap<INode, INode, IEdge> pre = new DoubleKeyCollectionMap<INode, INode, IEdge>();
        pre.add(graph.getPredecessors());

        final DoubleKeyCollectionMap<INode, INode, IEdge> succ = new DoubleKeyCollectionMap<INode, INode, IEdge>();
        succ.add(graph.getSuccessors());

        final CollectionMap<IEdge, IEdge> totalEdgeSplit = new CollectionMap<IEdge, IEdge>();
        for (final ImmutableSet<IEdge> subGraph : subGraphs) {
            final LinkedHashSet<IEdge> newSubGraph = new LinkedHashSet<IEdge>(subGraph);
            INode collapsedNode = this.selectNode(collapsedEdgeType, newSubGraph, protectedNodes, nodeTerms, pre, succ);
            while (collapsedNode != null) {
                final CollectionMap<IEdge, IEdge> edgeSplit =
                    this.collapseNode(idp,
                        collapsedEdgeType,
                        pre,
                        succ,
                        newEdgeConditions,
                        collapsedNode,
                        aborter);

                for (final Map.Entry<IEdge, ? extends Collection<IEdge>> edgeSplitEntry : edgeSplit.entrySet()) {
                    if (newSubGraph.remove(edgeSplitEntry.getKey())) {
                        newSubGraph.addAll(edgeSplitEntry.getValue());
                    }
                }

                // update total steps
                for (final Map.Entry<IEdge, ? extends Collection<IEdge>> newSplit : edgeSplit.entrySet()) {
                    if (originalEdges.contains(newSplit.getKey())) {
                        totalEdgeSplit.add(newSplit.getKey(), newSplit.getValue());
                    } else {
                        for (final Map.Entry<IEdge, ? extends Collection<IEdge>> totalSplitEntry : totalEdgeSplit.entrySet()) {
                            if (totalSplitEntry.getValue().remove(newSplit.getKey())) {
                                totalSplitEntry.getValue().addAll(newSplit.getValue());
                            }
                        }
                    }
                }

                collapsedNode = this.selectNode(collapsedEdgeType, newSubGraph, protectedNodes, nodeTerms, pre, succ);
            }
        }

        if (!totalEdgeSplit.isEmpty()) {
            return new CollapsedPathsResult(CollectionUtil.immutableCollectionMap(totalEdgeSplit),
                ImmutableCreator.create(newEdgeConditions.getMap()));
        } else {
            return null;
        }
    }

    private INode selectNode(final EdgeType collapsedEdgeType,
        final Set<IEdge> subGraph,
        final Set<INode> protectedNodes,
        final ImmutableMap<INode, ? extends ITerm<?>> nodeTerms, final DoubleKeyCollectionMap<INode, INode, IEdge> pre,
        final DoubleKeyCollectionMap<INode, INode, IEdge> succ) {
        final ArrayList<ArrayList<INode>> weightedCandidates = new ArrayList<ArrayList<INode>>();
        weightedCandidates.add(new ArrayList<INode>());
        weightedCandidates.add(new ArrayList<INode>());
        weightedCandidates.add(new ArrayList<INode>());

        final float MAX_EDGE_GAIN = 1;

        for (final Map.Entry<INode, CollectionMap<INode, IEdge>> preEntry : pre.entrySet()) {
            final INode node = preEntry.getKey();
            if (!protectedNodes.contains(node)
                    // all predecessor edges are in sub graph
                    && this.subGraphContainsAllEdges(subGraph, preEntry.getValue().allValues(), collapsedEdgeType)
                    // all successor edges are in sub graph
                    && (!succ.containsKey(node) || this.subGraphContainsAllEdges(subGraph, succ.get(node).allValues(), collapsedEdgeType))
                    // no self loop
                    && !preEntry.getValue().containsKey(node)) {
                int priority = 0;
                final int succEdgeCount = (succ.get(node) == null ? 0 : succ.get(node).size());
                final float newEdgeCount = preEntry.getValue().size() * succEdgeCount;
                final int oldEdgeCount = (preEntry.getValue().size() + succEdgeCount);
                final float edgeGain = oldEdgeCount != 0 ? newEdgeCount / oldEdgeCount : 0;

                if (edgeGain <= MAX_EDGE_GAIN) {
                    if (PredefinedUtil.hasPredefinedFunction(nodeTerms.get(node))) {
                        priority = 2;
                    } else if (preEntry.getValue().size() <= 1) {
                        priority = 1;
                    }

                    weightedCandidates.get(priority).add(node);
                }
            }
        }

        for (int priority = weightedCandidates.size() - 1; priority >= 0; priority--) {
            final ArrayList<INode> candidates = weightedCandidates.get(priority);
            if (!candidates.isEmpty()) {
                return candidates.get(0);
            }
        }

        return null;
    }

    private boolean subGraphContainsAllEdges(final Set<IEdge> subGraph,
        final Collection<IEdge> edges,
        final EdgeType collapsedEdgeType) {
        for (final IEdge edge : edges) {
            if (edge.type.isSubType(collapsedEdgeType) && !subGraph.contains(edge)) {
                return false;
            }
        }
        return true;
    }

    private CollectionMap<IEdge, IEdge> collapseNode (
        final IDPProblem idp,
        final EdgeType collapsedEdgeType,
        final DoubleKeyCollectionMap<INode, INode, IEdge> pre,
        final DoubleKeyCollectionMap<INode, INode, IEdge> succ,
        final EdgeConditionMap newEdgeConditions,
        final INode collapsedNode,
        final Abortion aborter) throws AbortionException {

        final ItpfFactory itpfFactory = idp.getItpfFactory();
        final FreshVarGenerator freshVars = idp.getIdpGraph().getFreshVarGenerator();
        final ImmutableMap<INode, VarRenaming> loopRenamings = idp.getIdpGraph().getLoopRenamings();

        final CollectionMap<INode, IEdge> pres = pre.remove(collapsedNode);
        final CollectionMap<INode, IEdge> succs = succ.remove(collapsedNode);

        final CollectionMap<IEdge, IEdge> edgeSplit = new CollectionMap<IEdge, IEdge>();

        final Set<IVariable<?>> nodeVars = loopRenamings.get(collapsedNode).getVariables();

        final List<ItpfSchedulerEdgeExecutorData> hiddenSimplificationWorkers = new ArrayList<ItpfSchedulerEdgeExecutorData>();

        PolyFactory polyFactory;
        if (idp.getPolyInterpretation() != null) {
            polyFactory = idp.getPolyInterpretation().getFactory();
        } else {
            polyFactory = null;
        }

        for (final Map.Entry<INode, Collection<IEdge>> preEntry : pres.entrySet()) {
            for (final IEdge preEdge : preEntry.getValue()) {
                succ.remove(preEdge.from, collapsedNode);
                if (preEdge.type.isSubType(collapsedEdgeType)) {
                    final Itpf preEdgeCondition = this.removeEdgeFromConditions(preEdge,
                        pre,
                        succ,
                        collapsedEdgeType,
                        newEdgeConditions,
                        edgeSplit);
                    if (succs != null) {
                        for (final Map.Entry<INode, Collection<IEdge>> succEntry : succs.entrySet()) {
                            for (final IEdge succEdge : succEntry.getValue()) {
                                if (succEdge.type.isSubType(collapsedEdgeType)) {
                                    Itpf succEdgeCondition = newEdgeConditions.get(succEdge);

                                    final IEdge newEdge = IEdge.create(preEdge.from, preEdge.fromPos, succEdge.to, collapsedEdgeType);
                                    if (newEdge.from.equals(newEdge.to)) {
                                        succEdgeCondition = succEdgeCondition.applySubstitution(loopRenamings.get(newEdge.to));
                                    }

                                    assert newEdge.to != collapsedNode : "unable to collapse node with self loop";

                                    final VarRenaming boundVarRenaming;
                                    Set<IVariable<?>> renamedNodeVars;

                                    final LinkedHashSet<IVariable<?>> alLBoundVars =
                                        new LinkedHashSet<IVariable<?>>();
                                    alLBoundVars.addAll(preEdgeCondition.getBoundVariables());
                                    alLBoundVars.addAll(succEdgeCondition.getBoundVariables());
                                    alLBoundVars.addAll(nodeVars);

                                    boundVarRenaming = ItpfUtil.getVariableRenaming(polyFactory, alLBoundVars, freshVars);

                                    renamedNodeVars = new LinkedHashSet<IVariable<?>>();
                                    for (final IVariable<?> nodeVar : nodeVars) {
                                        renamedNodeVars.add(boundVarRenaming.substituteTerm(nodeVar));
                                    }

                                    Itpf newEdgeCondition = itpfFactory.createAnd(
                                        freshVars,
                                        preEdgeCondition.applySubstitution(boundVarRenaming, true),
                                        succEdgeCondition.applySubstitution(boundVarRenaming, true));

                                    newEdgeCondition = itpfFactory.quantifyExist(renamedNodeVars, newEdgeCondition);

                                    hiddenSimplificationWorkers.add(new ItpfSchedulerEdgeExecutorData(idp,
                                        ItpfStrategy.HIDDEN_SIMPLIFICATION.getStrategy(),
                                        ImplicationType.SOUND,
                                        newEdge,
                                        newEdgeCondition,
                                        aborter));

                                    pre.add(newEdge.to, newEdge.from, newEdge);
                                    succ.add(newEdge.from, newEdge.to, newEdge);

                                    edgeSplit.add(preEdge, newEdge);
                                    edgeSplit.add(succEdge, newEdge);
                                }
                            }
                        }
                    }
                }
            }
        }

        MultithreadedExecutor.execute(hiddenSimplificationWorkers, aborter);

        for (final ItpfSchedulerEdgeExecutorData execData : hiddenSimplificationWorkers) {
            final Itpf cond = itpfFactory.createAnd(execData.getResult(), freshVars);
            newEdgeConditions.putOr(execData.getEdge(), cond);
        }

        if (succs != null) {
            for (final Map.Entry<INode, Collection<IEdge>> succEntry : succs.entrySet()) {
                for (final IEdge succEdge : succEntry.getValue()) {
                    pre.remove(succEdge.to, collapsedNode);
                    if (succEdge.type.isSubType(collapsedEdgeType)) {
                        this.removeEdgeFromConditions(succEdge,
                            pre,
                            succ,
                            collapsedEdgeType,
                            newEdgeConditions,
                            edgeSplit);
                    }
                }
            }
        }

        return edgeSplit;
    }

    private boolean allEdgesHaveType(final EdgeType collapsedEdgeType,
        final CollectionMap<INode, IEdge> pres) {
        for (final Map.Entry<INode, Collection<IEdge>> preEntry : pres.entrySet()) {
            for (final IEdge preEdge : preEntry.getValue()) {
                if (!preEdge.type.equals(collapsedEdgeType)) {
                    return false;
                }
            }
        }

        return true;
    }

    private Itpf removeEdgeFromConditions(final IEdge edge,
        final DoubleKeyCollectionMap<INode, INode, IEdge> preMap,
        final DoubleKeyCollectionMap<INode, INode, IEdge> succMap,
        final EdgeType collapsedEdgeType,
        final EdgeConditionMap newEdgeConditions,
        final CollectionMap<IEdge, IEdge> edgeSplit) {
        final Itpf res = newEdgeConditions.putFalse(edge);

        final EdgeType substractedType = edge.type.subtractType(collapsedEdgeType);

        if (substractedType != EdgeType.NO_EDGE) {
            final IEdge typeSubstractedEdge = IEdge.create(edge.from,
                edge.fromPos,
                edge.to,
                substractedType);

            edgeSplit.add(edge, typeSubstractedEdge);

            preMap.add(typeSubstractedEdge.to, typeSubstractedEdge.from, typeSubstractedEdge);
            succMap.add(typeSubstractedEdge.from, typeSubstractedEdge.to, typeSubstractedEdge);

            newEdgeConditions.putOr(
                typeSubstractedEdge,
                res);
        } else if (!edgeSplit.containsKey(edge)) {
            edgeSplit.add(edge, Collections.<IEdge>emptySet());
        }

        return res;
    }

    @Override
    public String getName() {
        return "NodeCollapsingPathGenerator";
    }

}
