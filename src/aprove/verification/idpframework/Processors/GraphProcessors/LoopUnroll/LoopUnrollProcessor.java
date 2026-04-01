package aprove.verification.idpframework.Processors.GraphProcessors.LoopUnroll;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.GraphProcessors.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class LoopUnrollProcessor extends AbstractGraphProcessor<Result, TIDPProblem> {

    public static class Arguments {
        LoopUnrollHeuristic heuristic = new SimpleLoopUnrollHeuristic(new SimpleLoopUnrollHeuristic.Arguments());
    }

    private final LoopUnrollHeuristic heuristic;

    @ParamsViaArgumentObject
    public LoopUnrollProcessor(final Arguments arguments) {
        super("LoopUnroll");
        this.heuristic = arguments.heuristic;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return CompatibleMarkClasses.LoopUnroll.isCompatible(mark);
    }

    @Override
    protected Result processIDPProblem(final TIDPProblem idp, final Abortion aborter)
            throws AbortionException {
        final ImmutableMap<INode, IEdge> loopNodes = ImmutableCreator.create(this.searchLoopNodes(idp.getIdpGraph()));

        final Set<INode> unrolledNodes = this.heuristic.getUnrolledNodes(idp, loopNodes, aborter);

        if (unrolledNodes.isEmpty()) {
            return ResultFactory.unsuccessful("no loops to unroll");
        }

        assert loopNodes.keySet().containsAll(unrolledNodes) : "every node which should be unrolled must have a loop";

        final IDPProblem newIDP = this.unrollLoops(idp, loopNodes, unrolledNodes, aborter);

        final LinkedHashMap<INode, Integer> unrollCounter = new LinkedHashMap<INode, Integer>(newIDP.getIdpGraph().getNodeUnrollCounter());
        unrollCounter.keySet().retainAll(unrolledNodes);


        return ResultFactory.proved(newIDP,
            YNMImplication.EQUIVALENT,
            new LoopUnrollProof(ImmutableCreator.create(unrollCounter)));
    }

    private IDPProblem unrollLoops(final IDPProblem idp,
        final ImmutableMap<INode, IEdge> loopNodes, final Set<INode> unrolledNodes,
        final Abortion aborter) {
        final IDependencyGraph idpGraph = idp.getIdpGraph();
        final ItpfFactory itpfFactory = idpGraph.getItpfFactory();

        final LinkedHashMap<IEdge, Itpf> newEdgeConditions = new LinkedHashMap<IEdge, Itpf>();

        for (final INode unrolledNode : unrolledNodes) {
            final IEdge loopEdge = loopNodes.get(unrolledNode);

            final VarRenaming loopRenaming = idpGraph.getLoopRenaming(unrolledNode);
            final VarRenaming varRenaming = ItpfUtil.getVariableRenaming(idpGraph.getPolyFactory(), idpGraph.getTerm(unrolledNode).getVariables(), idpGraph.getFreshVarGenerator());

            final List<ImmutablePair<IEdge, VarRenaming>> path = new ArrayList<ImmutablePair<IEdge,VarRenaming>>(3);
            path.add(new ImmutablePair<IEdge, VarRenaming>(loopEdge, varRenaming));
            path.add(new ImmutablePair<IEdge, VarRenaming>(loopEdge, loopRenaming));

            final VariableRenamedPath variableRenamedPath = VariableRenamedPath.create(idpGraph, ImmutableCreator.create(path));

            final Itpf unrolledCondition = idpGraph.itpfPath(variableRenamedPath, PathQuantificationMode.InnerSteps);

            if (loopEdge.type == EdgeType.INF) {
                newEdgeConditions.put(loopEdge, unrolledCondition);
            } else {
                newEdgeConditions.put(loopEdge, itpfFactory.createFalse());

                final IEdge nonInfEdge = loopEdge.subtractType(EdgeType.INF);
                newEdgeConditions.put(nonInfEdge, idpGraph.getCondition(loopEdge));

                final IEdge infEdge = loopEdge.changeType(EdgeType.INF);
                newEdgeConditions.put(infEdge, unrolledCondition);
            }
        }

        final IDependencyGraph newIdpGraph = idpGraph.change(
            null,
            newEdgeConditions,
            null,
            null,
            unrolledNodes,
            this);

        return idp.change(newIdpGraph);
    }

    private Map<INode, IEdge> searchLoopNodes(final IDependencyGraph idpGraph) {
        final Map<INode, IEdge> loopNodes = new LinkedHashMap<INode, IEdge>();
        // add nodes with loops
        for (final IEdge edge : idpGraph.getEdges()) {
            if (edge.type.isInf() && edge.from.equals(edge.to)) {
                loopNodes.put(edge.from, edge);
            }
        }

        // remove nodes with outgoing edges except the loop
        final Iterator<Entry<INode, IEdge>> loopNodesIterator = loopNodes.entrySet().iterator();
        nodeRemoval : while (loopNodesIterator.hasNext()) {
            final Entry<INode, IEdge> nodeEdge = loopNodesIterator.next();
            final ImmutableMap<INode, ImmutableSet<IEdge>> succs = idpGraph.getSuccessors(nodeEdge.getKey());

            for (final ImmutableSet<IEdge> sucEdges : succs.values()) {
                for (final IEdge succEdge : sucEdges) {
                    if (succEdge.type.isInf() && !succEdge.equals(nodeEdge.getValue())) {
                        loopNodesIterator.remove();
                        continue nodeRemoval;
                    }
                }
            }
        }

        return loopNodes;
    }

    public static class LoopUnrollProof extends DefaultProof {

        private final ImmutableMap<INode, Integer> unrollCounter;

        public LoopUnrollProof(final ImmutableLinkedHashMap<INode, Integer> unrollCounter) {
            this.unrollCounter = unrollCounter;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Unrolled loops on the following nodes (unroll counter):");
            sb.append(o.linebreak());
            for (final Map.Entry<INode, Integer> unroll : this.unrollCounter.entrySet()) {
                unroll.getKey().export(sb, o, level);
                sb.append(" (");
                sb.append(unroll.getValue());
                sb.append(")");
            }
            return sb.toString();
        }

    }

}
