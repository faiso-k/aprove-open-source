package aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.EdgeProviders;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Algorithms.Cap.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class CollapsableRewriteEdgesProvider implements CollapsableEdgesProvider {

    private final EdgeType colapsedEdgeType;

    public CollapsableRewriteEdgesProvider(final EdgeType colapsedEdgeType) {
        this.colapsedEdgeType = colapsedEdgeType;
        assert colapsedEdgeType.isRewrite() : "must collapse rewrite edges";
    }

    @Override
    public Set<ImmutableSet<IEdge>> getSubGraphs(final TIDPProblem idp, final Abortion aborter) {
        final Set<IEdge> res = new LinkedHashSet<IEdge>();

        for (final IEdge edge : idp.getIdpGraph().getEdges()) {
            if (edge.type.isRewrite() && edge.fromPos.isEmptyPosition()) {
                res.add(edge);
            }
        }

        return Collections.singleton(ImmutableCreator.create(res));
    }

    @Override
    public EdgeType getCollapsedEdgeType() {
        return this.colapsedEdgeType;
    }

    @Override
    public Set<INode> getProtectedNodes(final TIDPProblem idp, final Abortion aborter) throws AbortionException {
        final Set<INode> res = new LinkedHashSet<INode>();

        final IGraphCap cap = IGraphCap.Estimation.getEstimation(null);

        if (!this.collectProtectedNodeConditionNodes(idp, cap, res, aborter)) {
            res.addAll(idp.getIdpGraph().getNodes());
        } else if (!this.collectProtectedEdgeConditionNodes(idp, cap, res, aborter)) {
            res.addAll(idp.getIdpGraph().getNodes());
        }

        this.collectFinalNodes(idp.getIdpGraph(), res);

        return res;
    }

    private void collectFinalNodes(final IDependencyGraph idpGraph, final Set<INode> res) {
        final LinkedHashSet<INode> finalNodes = new LinkedHashSet<INode>(idpGraph.getNodes());
        for (final Map.Entry<INode, ImmutableMap<INode, ImmutableSet<IEdge>>> succEntry : idpGraph.getSuccessors().entrySet()) {
            if (!succEntry.getValue().isEmpty()) {
                finalNodes.remove(succEntry.getKey());
            }
        }

        res.addAll(finalNodes);
    }

    private boolean collectProtectedEdgeConditionNodes(final IDPProblem idp,
        final IGraphCap cap, final Set<INode> protectedNodes, final Abortion aborter) throws AbortionException {
        for (final Itpf formula : idp.getIdpGraph().getEdgeConditions().values()) {
            if (!this.collectProtectedNodes(idp.getIdpGraph(),
                    cap,
                    formula,
                    Collections.<ITerm<?>> emptySet(),
                    protectedNodes,
                    aborter)) {
                return false;
            }

            aborter.checkAbortion();
        }

        return true;
    }

    private boolean collectProtectedNodeConditionNodes(final IDPProblem idp,
        final IGraphCap cap, final Set<INode> protectedNodes, final Abortion aborter) throws AbortionException {
        for (final Itpf formula : idp.getIdpGraph().getNodeConditions().values()) {
            if (!this.collectProtectedNodes(idp.getIdpGraph(),
                    cap,
                    formula,
                    Collections.<ITerm<?>> emptySet(),
                    protectedNodes,
                    aborter)) {
                return false;
            }

            aborter.checkAbortion();
        }

        return true;
    }


    private boolean collectProtectedNodes(final IDependencyGraph idpGraph,
        final IGraphCap cap, final Itpf formula, final Set<ITerm<?>> sTerms,
        final Set<INode> protectedNodes, final Abortion aborter) throws AbortionException {
        for (final ItpfConjClause clause : formula.getClauses()) {
            final LinkedHashSet<ITerm<?>> completeS = new LinkedHashSet<ITerm<?>>(sTerms);
            completeS.addAll(clause.getS());

            for (final ItpfAtom atom : clause.getLiterals().keySet()) {
                if (atom.isImplication()) {
                    final ItpfImplication implication = (ItpfImplication) atom;
                    if (!this.collectProtectedNodes(idpGraph,
                            cap,
                            implication.getPrecondition(),
                            completeS,
                            protectedNodes, aborter)) {
                        return false;
                    }
                    if (!this.collectProtectedNodes(idpGraph,
                            cap,
                            implication.getConclusion(),
                            completeS,
                            protectedNodes, aborter)) {
                        return false;
                    }
                } else if (atom.isItp()) {
                    final ItpfItp itp = (ItpfItp) atom;
                    if (!this.collectProtectedNodes(idpGraph,
                            cap,
                            itp,
                            completeS,
                            protectedNodes,
                            aborter)) {
                        return false;
                    }

                } else if (atom.isTermUra()) {
                    final ItpfTermUra termUra = (ItpfTermUra) atom;
                    if (!this.collectProtectedNodes(idpGraph,
                            cap,
                            termUra,
                            completeS,
                            protectedNodes,
                            aborter)) {
                        return false;
                    }
                } else if (atom.isEdgeOrientation()) {
                    final ItpfEdgeOrientation edgeOrientation = (ItpfEdgeOrientation) atom;
                    protectedNodes.add(edgeOrientation.getEdge().from);
                    protectedNodes.add(edgeOrientation.getEdge().to);
                } else if (atom.isEdgeUra()) {
                    final ItpfEdgeUra edgeUra = (ItpfEdgeUra) atom;
                    protectedNodes.add(edgeUra.getEdge().from);
                } else if (atom.isNodeUra()) {
                    final ItpfNodeUra nodeUra = (ItpfNodeUra) atom;
                    protectedNodes.add(nodeUra.getNode());
                } else if (atom.isBoolPolyVar() || atom.isLogVar() || atom.isPoly()){
                    // nothing to do here
                } else {
                    // unknown atom type
                    throw new UnsupportedOperationException("unknown atom type: " + atom);
                }
            }
            aborter.checkAbortion();
        }
        return true;
    }

    private boolean collectProtectedNodes(final IDependencyGraph idpGraph,
        final IGraphCap cap,
        final ItpfTermUra termUra,
        final LinkedHashSet<ITerm<?>> sTerms,
        final Set<INode> protectedNodes,
        final Abortion aborter) {
        if (!sTerms.containsAll(termUra.getVariables())) {
            return false;
        }

        final Pair<? extends ITerm<?>, ImmutableMap<IPosition, ImmutableSet<IEdge>>> cappedTerm =
            cap.cap(idpGraph, sTerms, idpGraph.getFreshVarGenerator(), termUra.getTerm(), false);

        for (final ImmutableSet<IEdge> edges : cappedTerm.y.values()) {
            for (final IEdge edge : edges) {
                // maybe null for predefined functions
                if (edge != null) {
                    protectedNodes.add(edge.from);
                }
            }
        }

        return true;
    }

    private boolean collectProtectedNodes(final IDependencyGraph idpGraph,
        final IGraphCap cap,
        final ItpfItp itp,
        final LinkedHashSet<ITerm<?>> sTerms,
        final Set<INode> protectedNodes,
        final Abortion aborter) throws AbortionException {
        if (itp.getRelation().isRewriteRel()) {
            if (!sTerms.containsAll(itp.getL().getVariables())) {
                return false;
            }

            final IQTermSet q = idpGraph.getQ();

            final Pair<? extends ITerm<?>, ImmutableMap<IPosition, ImmutableSet<IEdge>>> cappedTerm =
                cap.cap(idpGraph, sTerms, idpGraph.getFreshVarGenerator(), itp.getL(), false);

            for (final ImmutableSet<IEdge> edges : cappedTerm.y.values()) {
                for (final IEdge edge : edges) {
                    if (edge != null) {
                        protectedNodes.add(edge.from);
                    }
                }
            }

            final LinkedHashSet<INode> reachableNodes = this.collectReachableNodes(idpGraph, cappedTerm.y.values(), aborter);
            if (sTerms.contains(itp.getR())) {
                for (final INode reachableNode : reachableNodes) {
                    final ITerm<?> nodeTerm = idpGraph.getTerm(reachableNode);

                    final Pair<? extends ITerm<?>, ImmutableMap<IPosition, ImmutableSet<IEdge>>> cappedNodeTerm =
                        cap.cap(idpGraph, sTerms, idpGraph.getFreshVarGenerator(), nodeTerm, false);

                    if (q.canBeRewritten(cappedNodeTerm.x)) {
                        protectedNodes.add(reachableNode);
                    }
                }
            } else if (!reachableNodes.isEmpty()) {
                protectedNodes.addAll(reachableNodes);
            }
        }

        return true;
    }

    private LinkedHashSet<INode> collectReachableNodes(final IDependencyGraph idpGraph,
        final Collection<ImmutableSet<IEdge>> edeCollections,
        final Abortion aborter) throws AbortionException {
        final LinkedHashSet<INode> reachableNodes = new LinkedHashSet<INode>();

        for (final ImmutableSet<IEdge> edges : edeCollections) {
            for (final IEdge edge : edges) {
                if (edge != null) {
                    // user defined application
                    this.collectReachableNodes(idpGraph, edge.from, reachableNodes, aborter);
                }
            }
            aborter.checkAbortion();
        }

        return reachableNodes;
    }

    private void collectReachableNodes(final IDependencyGraph idpGraph,
        final INode current,
        final Set<INode> reachableNodes,
        final Abortion aborter) throws AbortionException {
        if (reachableNodes.add(current)) {
            for (final ImmutableSet<IEdge> succEdges : idpGraph.getSuccessors(current).values()) {
                for (final IEdge edge : succEdges) {
                    this.collectReachableNodes(idpGraph, edge.to, reachableNodes, aborter);
                }
                aborter.checkAbortion();
            }
        }
    }

    @Override
    public String getName() {
        return "CollapsableRewriteEdgesProvider";
    }

}
