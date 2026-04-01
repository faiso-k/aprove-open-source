package aprove.verification.complexity.CIdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CIdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Algorithms.Cap.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 * copied from MPluecker, changed for complexity
 */
public class CIdtUsableRulesProcessor extends CIdtProcessor<Result> {

    public CIdtUsableRulesProcessor() {
        super("UsableRulesProcessor");
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    public boolean isCIdtApplicable(final CIdtProblem idp) {
        return true;
    }

    @Override
    protected Result processCIdtProblem(final CIdtProblem idt,
        final Abortion aborter) throws AbortionException {

        final Pair<Set<INode>, Set<IEdge>> reachables = this.getReachableEdges(idt);
        final Set<INode> reachableNodes = reachables.x;
        final Set<IEdge> reachableEdges = reachables.y;

        final Set<IEdge> deletedEdges = new LinkedHashSet<IEdge>();
        final Set<IEdge> newS = new LinkedHashSet<IEdge>(idt.getS());

        final IDependencyGraph graph = idt.getIdpGraph();
        final Itpf FALSE = idt.getItpfFactory().createFalse();

        final EdgeConditionMap deleteEdgesCondition = new EdgeConditionMap(idt.getItpfFactory(), idt.getIdpGraph().getFreshVarGenerator());
        for (final Map.Entry<IEdge, Itpf> edgeCondition : graph.getEdgeConditions().entrySet()) {
            final IEdge edge = edgeCondition.getKey();
            if (edge.type.isRewrite()) {
                if (!reachableEdges.contains(edge)) {
                    deletedEdges.add(edge);
                    deleteEdgesCondition.putFalse(edge);

                    final EdgeType nonRewriteType = edge.type.subtractType(EdgeType.REWRITE);
                    if (nonRewriteType != EdgeType.NO_EDGE) {
                        final IEdge nonRewriteEdge = edge.changeType(nonRewriteType);
                        deleteEdgesCondition.putOr(nonRewriteEdge, edgeCondition.getValue());
                        if (newS.contains(edge)) {
                            newS.remove(edge);
                            newS.add(nonRewriteEdge);
                        }
                    }
                }
            }
        }

        final Map<INode, Itpf> deleteNodesCondition = new LinkedHashMap<INode, Itpf>();

        for (final INode node : graph.getNodes()) {
            if (!reachableNodes.contains(node)) {
                deleteNodesCondition.put(node, FALSE);
            }
        }

        if (!deleteNodesCondition.isEmpty() || !deleteEdgesCondition.isEmpty()) {

            final IDependencyGraph newGraph = graph.change(
                deleteNodesCondition,
                deleteEdgesCondition.getMap(),
                null,
                null,
                null,
                this.mark);

            final CIdtProblem newIDP =
                idt.change(newGraph, ImmutableCreator.create(newS));

            final UsableRulesProof proof =
                new UsableRulesProof(ImmutableCreator.create(deleteNodesCondition.keySet()),
                    ImmutableCreator.create(deletedEdges));
            return ResultFactory.proved(newIDP, BothBounds.create(),
                proof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private Pair<Set<INode>, Set<IEdge>> getReachableEdges(final CIdtProblem idt) {
        final LinkedHashSet<IEdge> reachableEdges = new LinkedHashSet<IEdge>();
        final LinkedHashSet<INode> reachableNodes = new LinkedHashSet<INode>();

        final IDependencyGraph graph = idt.getIdpGraph();

        final IGraphCap capEstimation = IGraphCap.Estimation.getEstimation(null);

        Set<IEdge> edgesToVisit = new LinkedHashSet<IEdge>();

        for (final IEdge edge : idt.getIdpGraph().getEdges()) {
            if (edge.type.isInf()) {
                reachableNodes.add(edge.from);
                reachableNodes.add(edge.to);
                edgesToVisit.add(edge);
            }
        }


        final Set<IEdge> visitedEdges = new HashSet<IEdge>();
        final Set<INode> rewriteExandedNodes = new HashSet<INode>();
        Set<INode> nodesToVisit = new LinkedHashSet<INode>(reachableNodes);
        while (!edgesToVisit.isEmpty() || !nodesToVisit.isEmpty()) {

            final Set<INode> itpfEntryNodes = new LinkedHashSet<INode>();
            for (final IEdge edgeToVisit : edgesToVisit) {
                visitedEdges.add(edgeToVisit);
                this.collectEntryNodes(graph.getCondition(edgeToVisit), graph, capEstimation, itpfEntryNodes);
            }

            for (final INode nodeToVisit : nodesToVisit) {
                this.collectEntryNodes(graph.getCondition(nodeToVisit), graph, capEstimation, itpfEntryNodes);
            }

            itpfEntryNodes.removeAll(rewriteExandedNodes);

            final Set<INode> newEntryNodes = new LinkedHashSet<INode>();
            final Set<INode> newReachableNodes = new LinkedHashSet<INode>();;
            final LinkedHashSet<IEdge> newReachableEdges = new LinkedHashSet<IEdge>();;

            for (final INode itpfEntryNode : itpfEntryNodes) {
                this.collectEntryNodes(graph.getCondition(itpfEntryNode), graph, capEstimation, newEntryNodes);
                this.collectReachableEdges(itpfEntryNode, EdgeType.REWRITE, graph, newReachableEdges, newReachableNodes, rewriteExandedNodes);
                rewriteExandedNodes.add(itpfEntryNode);
            }

            reachableNodes.addAll(newReachableNodes);
            reachableEdges.addAll(newReachableEdges);

            nodesToVisit = newEntryNodes;
            nodesToVisit.addAll(newReachableNodes);
            nodesToVisit.removeAll(rewriteExandedNodes);

            edgesToVisit = newReachableEdges;
            edgesToVisit.removeAll(visitedEdges);
        }

        return new Pair<Set<INode>, Set<IEdge>>(reachableNodes, reachableEdges);
    }

    private void collectEntryNodes(final Itpf condition, final IDependencyGraph graph, final IGraphCap capEstimation, final Set<INode> itpfEntryNodes) {
      for (final ItpfConjClause clause : condition.getClauses()) {
          for (final ITerm<?> term : clause.getTerms()) {
                final Pair<? extends ITerm<?>, ImmutableMap<IPosition, ImmutableSet<IEdge>>> capResult =
                capEstimation.cap(graph, clause.getS(), graph.getFreshVarGenerator(), term, false);

                for (final ImmutableSet<IEdge> edges : capResult.y.values()) {
                    for (final IEdge edge : edges) {
                        if (edge != null) {
                            // user defined edge
                            itpfEntryNodes.add(edge.from);
                        }
                    }
                }
          }
      }

    }

    private void collectReachableEdges(final INode from, final EdgeType requiredEdgeType, final IDependencyGraph graph, final LinkedHashSet<IEdge> reachableEdges, final Set<INode> visitedNodes, final Set<INode> completelyExpandedNodes) {
        if (completelyExpandedNodes.contains(from)) {
            return;
        }
        completelyExpandedNodes.add(from);
        boolean completelyExpanded = true;
        for (final Map.Entry<INode, ImmutableSet<IEdge>> succEdges : graph.getSuccessors(from).entrySet()) {
            for (final IEdge succEdge : succEdges.getValue()) {
                if (!succEdge.type.isDisjoint(requiredEdgeType)) {
                    reachableEdges.add(succEdge);
                    visitedNodes.add(succEdge.from);
                    visitedNodes.add(succEdge.to);
                    this.collectReachableEdges(succEdge.to, requiredEdgeType, graph, reachableEdges, visitedNodes, completelyExpandedNodes);
                } else {
                    completelyExpanded = false;
                }
            }
        }

        if (!completelyExpanded) {
            completelyExpandedNodes.remove(from);
        }
    }

    private static class UsableRulesProof extends Proof.DefaultProof {

        private final ImmutableSet<INode> deletedNodes;
        private final ImmutableSet<IEdge> deletedEdges;

        private UsableRulesProof(
                final ImmutableSet<INode> deletedNodes,
                final ImmutableSet<IEdge> deletedEdges) {
            this.deletedNodes = deletedNodes;
            this.deletedEdges = deletedEdges;
        }

        private static final Citation[] citations =
            new Citation[] {  };

        @Override
        public final String toString() {
            return this.export(new PLAIN_Util());
        }

        @Override
        public final String export(final Export_Util o) {
            return this.export(o, IDPExportable.DEFAULT_LEVEL);
        }

        @Override
        public final String export(final Export_Util o,
            final VerbosityLevel verbosityLevel) {
            final StringBuilder sb = new StringBuilder();
            this.export(sb, o, verbosityLevel);
            return sb.toString();
        }

        public void export(final StringBuilder sb,
            final Export_Util o,
            final VerbosityLevel level) {
            sb.append("Deleted ");
            sb.append(this.deletedNodes.size());
            sb.append(" not reachable nodes:");
            sb.append(o.linebreak());
            sb.append(o.set(this.deletedNodes, Export_Util.NICE_SET));
            sb.append(o.linebreak());

            sb.append(o.linebreak());
            sb.append("Deleted/Changed ");
            sb.append(this.deletedEdges.size());
            sb.append(" not reachable edges:");
            sb.append(o.linebreak());
            sb.append(o.set(this.deletedEdges, Export_Util.NICE_SET));
            sb.append(o.linebreak());

        }
    }
}
