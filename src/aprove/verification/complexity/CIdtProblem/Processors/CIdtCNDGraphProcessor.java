package aprove.verification.complexity.CIdtProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CIdtProblem.*;
import aprove.verification.complexity.CIdtProblem.Utility.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.GraphProcessors.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 */
public class CIdtCNDGraphProcessor extends AbstractSchedulerGraphProcessor<Result, CIdtProblem> {

    private enum GraphStrategy {
        WORK_ON_ALL, DELETE_OR_DO_NOT_CHANGE
    };

    private final GraphStrategy graphStrategy;

    @ParamsViaArgumentObject
    public CIdtCNDGraphProcessor(Arguments arguments) {
        super("CIdtCNDGraphProcessor", arguments.strategy.getStrategy());
        this.graphStrategy = arguments.graphStrategy;
    }

    @Override
    protected Result processResult(CIdtProblem idt,
        List<SchedulerExecutorData<Itpf, GenericItpfRule<?>, ?>> workers,
        Abortion aborter) {

        if (Globals.useAssertions) {
            for (SchedulerExecutorData<Itpf, GenericItpfRule<?>, ?> worker : workers) {
                assert(worker.getProof().getTotalImplication().isSound());
            }
        }

        final List<ItpfSchedulerEdgeProof> edgeProofs =
            new ArrayList<ItpfSchedulerEdgeProof>(
                idt.getIdpGraph().getEdges().size());
        final List<ItpfSchedulerNodeProof> nodeProofs =
            new ArrayList<ItpfSchedulerNodeProof>(
                idt.getIdpGraph().getNodes().size());

        final IDependencyGraph graph = idt.getIdpGraph();

        final EdgeConditionMap newEdgeFormulas =
            new EdgeConditionMap(graph.getItpfFactory(), graph.getFreshVarGenerator());

        final Map<INode, Itpf> newNodeFormulas = new LinkedHashMap<INode, Itpf>();

        final ItpfFactory itpfFactory = idt.getIdpGraph().getItpfFactory();

        for (final SchedulerExecutorData<Itpf, GenericItpfRule<?>, ?> worker : workers) {
            if (worker.isSuccessfull()) {
                if (this.graphStrategy == GraphStrategy.WORK_ON_ALL) {
                    if (worker.isEdgeData()) {
                        final ItpfSchedulerEdgeExecutorData edgeWorker = (ItpfSchedulerEdgeExecutorData) worker;
                        final Itpf newFormula = itpfFactory.createAnd(worker.getResult());
                        newEdgeFormulas.putReplace(edgeWorker.getEdge(), newFormula);
                        edgeProofs.add(edgeWorker.getProof());
                    } else if (worker.isNodeData()) {
                        final ItpfSchedulerNodeExecutorData ruleWorker = (ItpfSchedulerNodeExecutorData) worker;
                        newNodeFormulas.put(ruleWorker.getNode(), itpfFactory.createAnd(worker.getResult()));
                        nodeProofs.add(ruleWorker.getProof());
                    }
                } else if (this.graphStrategy == GraphStrategy.DELETE_OR_DO_NOT_CHANGE) {
                    if (worker.isEdgeData()) {
                        final ItpfSchedulerEdgeExecutorData edgeWorker = (ItpfSchedulerEdgeExecutorData) worker;
                        final Itpf newFormula = itpfFactory.createAnd(worker.getResult());
                        if (newFormula.isFalse()) {
                            newEdgeFormulas.putReplace(edgeWorker.getEdge(), newFormula);
                            edgeProofs.add(edgeWorker.getProof());
                        }
                    } else if (worker.isNodeData()) {
                        final ItpfSchedulerNodeExecutorData ruleWorker = (ItpfSchedulerNodeExecutorData) worker;
                        final Itpf newFormula = itpfFactory.createAnd(worker.getResult());
                        if (newFormula.isFalse()) {
                            newNodeFormulas.put(ruleWorker.getNode(), newFormula);
                            nodeProofs.add(ruleWorker.getProof());
                        }
                    }
                }
            }
        }

        if (newEdgeFormulas.isEmpty() && newNodeFormulas.isEmpty()) {
            return ResultFactory.unsuccessful();
        } else {
            final Proof proof =
                new CIdtCNDGraphProof("CIdtCNDGraphProcessor",
                    ImmutableCreator.create(nodeProofs),
                    ImmutableCreator.create(edgeProofs));

            IDependencyGraph newGraph = null;
            try {
                newGraph =
                    idt.getIdpGraph().change(
                        newNodeFormulas,
                        newEdgeFormulas.getMap(),
                        null,
                        null,
                        null,
                        this.mark);
            } catch (final AssertionError e) {
                if (Globals.DEBUG_MARCEL) {
                    System.err.println(proof);
                }
                throw e;
            }

            ImmutableSet<IEdge> newS = CIdtProblem.cleanupS(newGraph, idt.getS(), idt.getK());

            final Set<Mark<?>> usedMarks = new HashSet<Mark<?>>();
            final Set<GenericItpfRule<?>> allRules = this.strategy.getAllRules();
            for (final GenericItpfRule<?> rule : allRules) {
                usedMarks.addAll(rule.getUsedMarks());
            }

            return ResultFactory.proved(
                idt.change(newGraph, newS), UpperBound.create(new SumComputation(ComplexityValue.constant())), proof);
        }
    }

    @Override
    public boolean isIDPApplicable(IDPProblem idp) {
        return (idp instanceof CIdtProblem);
    }

    @Override
    public boolean isCompatible(Mark<?> mark) {
        return false;
    }

    public static class Arguments {
        public CNDStrategy  strategy = CNDStrategy.CND_DefaultStrategy;
        public GraphStrategy  graphStrategy = GraphStrategy.WORK_ON_ALL;
    }

    protected static class CIdtCNDGraphProof extends AbstractSchedulerGraphProcessor.ItpfSchedulerGraphProof {

        public CIdtCNDGraphProof(String description,
                ImmutableList<ItpfSchedulerNodeProof> ruleProofs,
                ImmutableList<ItpfSchedulerEdgeProof> edgeProofs) {
            super(description, ruleProofs, edgeProofs);
        }

    }

}
