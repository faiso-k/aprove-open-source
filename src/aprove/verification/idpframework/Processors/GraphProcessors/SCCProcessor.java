package aprove.verification.idpframework.Processors.GraphProcessors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;
/**
 * @author Martin Pluecker
 */
public class SCCProcessor extends TIDPProcessor<Result> {

    final static Set<EdgeType> INF_EDGE_TYPES = SCCProcessor.getInfiniteEdgeTypes();

    public SCCProcessor() {
        super("SCCProcessor");
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
        Set<IDPSubGraph> sccs =
            new LinkedHashSet<IDPSubGraph>();

        final IDependencyGraph graph = idp.getIdpGraph();
        boolean changed = false;
        int oldNodeCount = 0;

        final EdgeConditionMap newEdgeConditions =
            new EdgeConditionMap(idp.getIdpGraph().getItpfFactory(), null);

        final Map<IDPSubGraph, ImmutableList<IDPSubGraph>> splitting =
            new LinkedHashMap<IDPSubGraph, ImmutableList<IDPSubGraph>>();

//        final Set<IEdge> removedEdges = new HashSet<IEdge>();
//        for (final IEdge edge : graph.getEdges()) {
//            if (edge.type.isInf()) {
//                removedEdges.add(edge);
//            }
//        }

        for (final IDPSubGraph subGraph : idp.getSubGraphs()) {
            oldNodeCount += subGraph.size();
            final ImmutableList<IDPSubGraph> scs =
                graph.getEdgeSccs(subGraph);

            splitting.put(subGraph, scs);

            sccs.addAll(scs);
//            for (final IDPSubGraph scc : scs) {
//                removedEdges.removeAll(scc.getEdges());
//            }

            if (scs.size() != 1 || !scs.get(0).equals(subGraph)) {
                changed = true;
            }
        }

//        changed = changed || !removedEdges.isEmpty();
//
//        removeEdges(graph, newEdgeConditions, removedEdges);

        sccs = GraphUtil.cleanupSubGraphs(sccs);

        int newNodeCount = 0;
        for (final IDPSubGraph sc : sccs) {
            newNodeCount += sc.size();
        }

        if (changed) {
            final IDependencyGraph newGraph =
                graph.change(
                    Collections.<INode, Itpf> emptyMap(),
                    newEdgeConditions.getMap(),
                    null,
                    null,
                    null,
                    this.mark);

            final IDPProblem newIDP =
                idp.change(newGraph, ImmutableCreator.create(sccs));

            final IDependencyGraphProof proof =
                new IDependencyGraphProof(ImmutableCreator.create(splitting),
                    sccs.size(), oldNodeCount - newNodeCount);
            return ResultFactory.proved(newIDP, YNMImplication.EQUIVALENT,
                proof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private static Set<EdgeType> getInfiniteEdgeTypes() {
        final Set<EdgeType> edgeTypes = new HashSet<EdgeType>();

        for (final EdgeType type : EdgeType.values()) {
            if (type.isInf()) {
                edgeTypes.add(type);
            }
        }
        return edgeTypes;
    }

    private void removeEdges(final IDependencyGraph graph,
        final EdgeConditionMap newEdgeConditions,
        final Collection<IEdge> removedEdges) {
        for (final IEdge edge : removedEdges) {
            final IEdge newEdge = IEdge.create(edge.from, edge.fromPos, edge.to, edge.type.subtractType(EdgeType.INF));
            newEdgeConditions.putOr(newEdge, graph.getCondition(edge));
            newEdgeConditions.putFalse(edge);
        }
    }

    private static class IDependencyGraphProof extends Proof.DefaultProof {

        private final int nrSccs;
        private final int lessNodes;
        private final ImmutableMap<IDPSubGraph, ImmutableList<IDPSubGraph>> splitting;

        private IDependencyGraphProof(
                final ImmutableMap<IDPSubGraph, ImmutableList<IDPSubGraph>> splitting,
                final int nrSccs, final int lessNodes) {
            this.splitting = splitting;
            this.nrSccs = nrSccs;
            this.lessNodes = lessNodes;
        }

        private static final Citation[] citations =
            new Citation[] { Citation.LPAR04, Citation.FROCOS05,
                Citation.EDGSTAR };

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
            sb.append("The approximation of the Dependency Graph ");
            sb.append(o.cite(IDependencyGraphProof.citations));
            sb.append(" contains ");
            sb.append(this.nrSccs);
            sb.append(" SCC");
            if (this.nrSccs != 1) {
                sb.append("s");
            }
            if (this.lessNodes > 0) {
                sb.append(" with ");
                sb.append(this.lessNodes);
                sb.append(" less node");
                if (this.lessNodes == 1) {
                    sb.append(".");
                } else {
                    sb.append("s.");
                }
            } else {
                sb.append(".");
            }
            if (!this.splitting.isEmpty()) {
                sb.append(o.linebreak());
            }
            for (final Map.Entry<IDPSubGraph, ImmutableList<IDPSubGraph>> split : this.splitting.entrySet()) {
                if (split.getValue().isEmpty()) {
                    sb.append("Removed ");
                } else {
                    sb.append("Splitted ");
                }
                split.getKey().export(sb, o, level);
                if (!split.getValue().isEmpty()) {
                    sb.append(" ");
                    sb.append(o.rightarrow());
                    sb.append(" ");
                    boolean first = true;
                    for (final IDPSubGraph newScc : split.getValue()) {
                        if (first) {
                            sb.append("[ ");
                        } else {
                            sb.append(", [ ");
                        }
                        first = false;
                        newScc.export(sb, o, level);
                        sb.append("]");
                    }
                }
                sb.append(o.linebreak());
            }
        }
    }

}
