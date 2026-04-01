package aprove.verification.complexity.CIdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CIdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class CIdtNodeSplitProcessor extends CIdtProcessor<Result> {

    public CIdtNodeSplitProcessor() {
        super("CIdtSSplit");
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @SuppressWarnings("unchecked")
    @Override
    protected Result processCIdtProblem(final CIdtProblem idt,
        final Abortion aborter) throws AbortionException {

        boolean successful = false;

        final Set<INode> newNodes = new LinkedHashSet<>();
        final Set<IEdge> newEdges = new LinkedHashSet<>();

        final IDependencyGraph graph = idt.getIdpGraph();
        final ItpfFactory itpfFactory = graph.getItpfFactory();
        final PolyFactory polyFactory = graph.getPolyFactory();

        final Set<IEdge> newS = new LinkedHashSet<>(idt.getS());
        final Map<INode, Itpf> newNodeConditions = new LinkedHashMap<>();
        newNodeConditions.putAll(graph.getNodeConditions());
        final Map<IEdge, Itpf> newEdgeConditions = new LinkedHashMap<>();
        newEdgeConditions.putAll(graph.getEdgeConditions());
        final Map<INode, ITerm<?>> nodesToTerms = new LinkedHashMap<>();
        nodesToTerms.putAll(idt.getIdpGraph().getNodeMap());

        final Map<IFunctionSymbol<?>, ImmutableSet<INode>> newInitialRewriteNodes =
            new LinkedHashMap<>();
        newInitialRewriteNodes.putAll(graph.getInitialRewriteNodes());

        final Map<INode, Integer> newNodeUnrollCounter = new LinkedHashMap<>();
        newNodeUnrollCounter.putAll(graph.getNodeUnrollCounter());

        final Map<INode, VarRenaming> newLoopRenamings = new LinkedHashMap<>();
        newLoopRenamings.putAll(graph.getLoopRenamings());

        int newNodeId = 0;
        for (final INode node : graph.getNodes()) {
            if (node.id >= newNodeId) {
                newNodeId = node.id + 1;
            }
        }

        for (final IEdge edge : idt.getS()) {
            if (graph.getCondition(edge).getClauses().size() > 1) {

                successful = true;
                newEdgeConditions.put(edge, itpfFactory.createFalse());
                newS.remove(edge);

                final INode nodeToSplit = edge.from;
                final ITerm<?> nodeTermFrom =
                    nodesToTerms.get(edge.from).getSubterm(edge.fromPos);

                final VarRenaming loopRenFrom =
                    graph.getLoopRenaming(nodeToSplit);

                final Map<IVariable<?>, IVariable<?>> loopRenRevMap =
                    new LinkedHashMap<>();

                for (final Map.Entry<IVariable<?>, ? extends IVariable<?>> entry : loopRenFrom.getMap().entrySet()) {
                    loopRenRevMap.put(entry.getValue(), entry.getKey());
                }

                final VarRenaming oldLoopRenReversed =
                    VarRenaming.create(ImmutableCreator.create(loopRenRevMap),
                        false, polyFactory);

                //create new Nodes
                for (final ItpfConjClause conjClause : graph.getCondition(edge)) {

                    final VarRenaming ren =
                        graph.getFreshVarsRenaming(nodeTermFrom);
                    final INode newNode = INode.create(newNodeId);
                    newNodes.add(newNode);
                    newNodeId++;

                    final ITerm<?> newNodeTerm =
                        nodeTermFrom.applySubstitution(ren);

                    final VarRenaming loopRen =
                        graph.getFreshVarsRenaming(newNodeTerm);

                    newNodeConditions.put(newNode,
                        graph.getCondition(nodeToSplit).applySubstitution(ren));
                    newNodeUnrollCounter.put(newNode, 0);

                    newLoopRenamings.put(newNode, loopRen);

                    nodesToTerms.put(newNode, newNodeTerm);

                    //createEdgeFromNewNode

                    final IEdge edgeFromNewNode =
                        IEdge.create(newNode, IPosition.EMPTY, edge.to,
                            edge.type);

                    newEdges.add(edgeFromNewNode);

                    final ImmutableList<ItpfQuantor> quantors =
                        graph.getCondition(edge).getQuantification();

                    Itpf conditionFromNewNode =
                        itpfFactory.create(quantors, conjClause).applySubstitution(
                            ren, false);

                    // For self loops. we need to rename our variables back
                    if (edge.from == edge.to) {
                        conditionFromNewNode =
                            itpfFactory.create(quantors, conjClause).applySubstitution(
                                oldLoopRenReversed, false);
                    }

                    conditionFromNewNode =
                        conditionFromNewNode.applySubstitution(ren, false);

                    final VarRenaming renameBoundedVar =
                        ItpfUtil.getVariableRenaming(polyFactory,
                            conditionFromNewNode.getBoundVariables(),
                            graph.getFreshVarGenerator());

                    conditionFromNewNode =
                        conditionFromNewNode.applySubstitution(
                            renameBoundedVar, true);

                    //add edgeFromeNewNode to S holding the old disjunct
                    newS.add(edgeFromNewNode);

                    newEdgeConditions.put(edgeFromNewNode, conditionFromNewNode);

                    // create edge to new node: f(x) -> f(x')
                    //and condition: x = x'
                    final IEdge edgeToNewNode =
                        IEdge.create(nodeToSplit, edge.fromPos, newNode,
                            EdgeType.INF);

                    newEdges.add(edgeToNewNode);

                    final Itpf conditionToNewNode =
                        this.createConditionTo(nodeTermFrom, ren, itpfFactory);

                    newEdgeConditions.put(edgeToNewNode, conditionToNewNode);

                }
            }

        }

        if (successful) {
            final IDependencyGraph newGraph =
                this.createNewGraph(graph, ImmutableCreator.create(nodesToTerms),
                    ImmutableCreator.create(newNodeConditions),
                    ImmutableCreator.create(newInitialRewriteNodes),
                    ImmutableCreator.create(newEdgeConditions),
                    ImmutableCreator.create(newNodeUnrollCounter),
                    ImmutableCreator.create(newLoopRenamings));

            final CIdtProblem newCIdt =
                idt.change(newGraph, ImmutableCreator.create(newS), idt.getK());
            return ResultFactory.proved(newCIdt, BothBounds.create(),
                new CIdtNodeSplitProof(ImmutableCreator.create(newNodes),
                    ImmutableCreator.create(newEdges)));
        } else {
            return ResultFactory.unsuccessful();
        }

    }

    private Itpf createConditionTo(final ITerm<?> nodeTermFrom,
        final VarRenaming ren,
        final ItpfFactory itpfFactory) {
        final Map<ItpfAtom, Boolean> literals = new LinkedHashMap<>();

        for (final IVariable<?> var : nodeTermFrom.getVariables()) {
            final ItpfItp varEq =
                ItpfItp.create(var, RelDependency.Increasing,
                    IActiveContext.EMPTY_CONTEXT, ItpRelation.EQ,
                    ren.substituteTerm(var), RelDependency.Increasing,
                    IActiveContext.EMPTY_CONTEXT, itpfFactory);

            literals.put(varEq, true);
        }
        return itpfFactory.create(ItpfConjClause.create(
            ImmutableCreator.create(literals), ITerm.EMPTY_SET, itpfFactory));
    }

    private IDependencyGraph createNewGraph(final IDependencyGraph graph,
        final ImmutableMap<INode, ITerm<?>> newNodes,
        final ImmutableMap<INode, Itpf> newNodeConditions,
        final ImmutableMap<IFunctionSymbol<?>, ImmutableSet<INode>> newInitialRewriteNodes,
        final ImmutableMap<IEdge, Itpf> newEdgeConditions,
        final ImmutableMap<INode, Integer> newNodeUnrollCounter,
        final ImmutableMap<INode, VarRenaming> newLoopRenamings) {

        return IDependencyGraph.create(graph.getPredefinedMap(), graph.getQ(),
            graph.getItpfFactory(), graph.getPolyInterpretation(), newNodes,
            newNodeConditions, newInitialRewriteNodes, newNodeUnrollCounter,
            newLoopRenamings, newEdgeConditions, graph.getFreshVarGenerator());
    }

    @Override
    protected boolean isCIdtApplicable(final CIdtProblem idt) {
        return true;
    }

    protected static class CIdtNodeSplitProof extends DefaultProof {

        private final ImmutableSet<INode> newNodes;
        private final ImmutableSet<IEdge> newEdges;

        public CIdtNodeSplitProof(final ImmutableSet<INode> deletedNodes,
                final ImmutableSet<IEdge> deletedEdges) {
            this.newNodes = deletedNodes;
            this.newEdges = deletedEdges;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("new nodes:");
            sb.append(eu.linebreak());
            sb.append(eu.set(this.newNodes, Export_Util.NICE_SET));

            sb.append(eu.linebreak());
            sb.append(eu.linebreak());

            sb.append("new edges:");
            sb.append(eu.linebreak());
            sb.append(eu.set(this.newEdges, Export_Util.NICE_SET));
            return sb.toString();
        }

    }

}
