package aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.GraphProcessors.*;
import aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.EdgeProviders.*;
import aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.PathGenerators.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public abstract class AbstractPathCollapse extends AbstractGraphProcessor<Result, TIDPProblem> {

    private final CollapsableEdgesProvider collapsableProvider;
    private final CollapsablePathGenerator pathGenerator;
    private final float maxEdgeGain;

    public AbstractPathCollapse(final String description,
        final CollapsableEdgesProvider collapsableProvider,
        final CollapsablePathGenerator pathGenerator,
        final float maxEdgeGain) {
        super(description);
        this.collapsableProvider = collapsableProvider;
        this.pathGenerator = pathGenerator;
        this.maxEdgeGain = maxEdgeGain;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    protected Result processIDPProblem(final TIDPProblem idp,
        final Abortion aborter) throws AbortionException {
        final CollapsedPathsResult collapsedPathsResult =
            this.pathGenerator.collapsePaths(idp, this.collapsableProvider, this.maxEdgeGain, aborter);

        if (collapsedPathsResult!= null) {
            final IDPProblem newIDP = this.createResult(idp,
                collapsedPathsResult);

            final PathCollapseProof proof =
                new PathCollapseProof(
                    collapsedPathsResult,
                    this.collapsableProvider,
                    this.pathGenerator);
            return ResultFactory.proved(newIDP, YNMImplication.EQUIVALENT,
                proof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    protected IDPProblem createResult(final TIDPProblem idp,
        final CollapsedPathsResult collapsResult) {
        final Set<IDPSubGraph> newIdpSubGraphs = new LinkedHashSet<IDPSubGraph>();

        for (final IDPSubGraph idpSubGraph : idp.getSubGraphs()) {
            final LinkedHashSet<IEdge> newSubGraph = new LinkedHashSet<IEdge>();
            for (final IEdge edge : idpSubGraph.getEdges()) {
                final ImmutableSet<IEdge> splitEdges = collapsResult.edgeSplit.get(edge);
                if (splitEdges != null) {
                    for (final IEdge splitEdge : splitEdges) {
                        if (splitEdge.type.isInf()) {
                            final Itpf newEdgeCondition = collapsResult.newEdgeConditions.get(splitEdge);
                            if (newEdgeCondition == null || !newEdgeCondition.isFalse()) {
                                newSubGraph.add(splitEdge);
                            }
                        }
                    }
                } else {
                    final Itpf newEdgeCondition = collapsResult.newEdgeConditions.get(edge);
                    if (newEdgeCondition == null || !newEdgeCondition.isFalse()) {
                        newSubGraph.add(edge);
                    }
                }
            }

            newIdpSubGraphs.add(new IDPSubGraph(ImmutableCreator.create(newSubGraph)));
        }

        final IDependencyGraph graph = idp.getIdpGraph();
        final LinkedHashMap<INode, Itpf> removedNodes = new LinkedHashMap<INode, Itpf>();
        removeableNodeSearch : for (final INode node : graph.getNodes()) {
            for (final Collection<IEdge> preEdges : graph.getPredecessors(node).values()) {
                for (final IEdge edge : preEdges) {
                    final Itpf condition = collapsResult.newEdgeConditions.get(edge);
                    if (condition == null || !condition.isFalse()) {
                        continue removeableNodeSearch;
                    }
                }
            }

            for (final Collection<IEdge> succEdges : graph.getSuccessors(node).values()) {
                for (final IEdge edge : succEdges) {
                    final Itpf condition = collapsResult.newEdgeConditions.get(edge);
                    if (condition == null || !condition.isFalse()) {
                        continue removeableNodeSearch;
                    }
                }
            }

            for (final Map.Entry<IEdge, Itpf> newEdge : collapsResult.newEdgeConditions.entrySet()) {
                final IEdge edge = newEdge.getKey();
                if ((edge.from.equals(node) || edge.to.equals(node)) && !newEdge.getValue().isFalse()) {
                    continue removeableNodeSearch;
                }
            }

            removedNodes.put(node, graph.getItpfFactory().createFalse());
        }

        final IDependencyGraph newGraph = idp.getIdpGraph().change(
            removedNodes,
            collapsResult.newEdgeConditions,
            null,
            null,
            null,
            this);

        return idp.change(newGraph,
            ImmutableCreator.create(newIdpSubGraphs));
    }

    private static class PathCollapseProof extends Proof.DefaultProof {

        private final CollapsedPathsResult collapsResult;
        private final CollapsableEdgesProvider collapsableProvider;
        private final CollapsablePathGenerator pathGenerator;

        private PathCollapseProof (
                final CollapsedPathsResult collapsResult, final CollapsableEdgesProvider collapsableProvider, final CollapsablePathGenerator pathGenerator) {
            this.collapsResult = collapsResult;
            this.collapsableProvider = collapsableProvider;
            this.pathGenerator = pathGenerator;
        }

        @Override
        public final String export(final Export_Util o,
            final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Collapsable nodes were generated by ");
            sb.append(this.collapsableProvider.getName());
            sb.append(".");
            sb.append(o.newline());
            sb.append("Collapsable edges were generated by ");
            sb.append(this.pathGenerator.getName());

            if (!this.collapsResult.edgeSplit.isEmpty()) {
                sb.append(":");
                sb.append(o.newline());
                sb.append(o.linebreak());
                final ArrayList<List<String>> splitTable = new ArrayList<List<String>>(this.collapsResult.edgeSplit.size());

                for (final Map.Entry<IEdge, ImmutableSet<IEdge>> edgeSplit : this.collapsResult.edgeSplit.entrySet()) {
                    final ArrayList<String> splitRow = new ArrayList<String>(edgeSplit.getValue().size());
                    splitRow.add(edgeSplit.getKey().export(o, VerbosityLevel.LOW));

                    final StringBuilder colStringBuilder = new StringBuilder();
                    boolean first = true;
                    for (final IEdge edge : edgeSplit.getValue()) {
                        if (!first) {
                            colStringBuilder.append(", ");
                        }
                        first = false;
                        colStringBuilder.append(edge.export(o));
                    }

                    splitRow.add(colStringBuilder.toString());

                    splitTable.add(splitRow);
                }

                sb.append(o.table(splitTable));
            } else {
                sb.append("no edges were collapsed");
            }

            return sb.toString();
        }
    }

}
