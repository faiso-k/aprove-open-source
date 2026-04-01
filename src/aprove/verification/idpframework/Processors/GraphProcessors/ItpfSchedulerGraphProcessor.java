/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Processors.GraphProcessors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Logic.*;
import immutables.*;

public class ItpfSchedulerGraphProcessor extends
        AbstractSchedulerGraphProcessor<Result, TIDPProblem> {

    public static final Integer MAIN_TYPE = Integer.valueOf(0);

    @ParamsViaArguments(value = { "strategy" })
    public ItpfSchedulerGraphProcessor(final ItpfStrategy strategy) {
        super("ItpfGraphProcessor", strategy.getStrategy());
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
    protected Result processResult(final TIDPProblem idp,
        final List<SchedulerExecutorData<Itpf, GenericItpfRule<?>, ?>> workers,
        final Abortion aborter) {
        final List<ItpfSchedulerEdgeProof> edgeProofs =
            new ArrayList<ItpfSchedulerEdgeProof>(
                idp.getIdpGraph().getEdges().size());
        final List<ItpfSchedulerNodeProof> nodeProofs =
            new ArrayList<ItpfSchedulerNodeProof>(
                idp.getIdpGraph().getNodes().size());

        final IDependencyGraph graph = idp.getIdpGraph();

        final EdgeConditionMap newEdgeFormulas =
            new EdgeConditionMap(graph.getItpfFactory(), graph.getFreshVarGenerator());

        final Map<INode, Itpf> newNodeFormulas = new LinkedHashMap<INode, Itpf>();

        final ItpfFactory itpfFactory = idp.getIdpGraph().getItpfFactory();

        boolean sound = true;
        boolean complete = true;
        for (final SchedulerExecutorData<Itpf, GenericItpfRule<?>, ?> worker : workers) {
            if (worker.isSuccessfull()) {
                final ImplicationType totalImplication = worker.getProof().getTotalImplication();
                sound = sound && totalImplication.isSound();
                complete = complete && totalImplication.isComplete();
                if (worker.isEdgeData()) {
                    final ItpfSchedulerEdgeExecutorData edgeWorker =
                        (ItpfSchedulerEdgeExecutorData) worker;
                    final Itpf newFormula = itpfFactory.createAnd(worker.getResult());
                    newEdgeFormulas.putReplace(edgeWorker.getEdge(),
                        newFormula);
                    edgeProofs.add(edgeWorker.getProof());
                } else if (worker.isNodeData()) {
                    final ItpfSchedulerNodeExecutorData ruleWorker =
                        (ItpfSchedulerNodeExecutorData) worker;
                    newNodeFormulas.put(ruleWorker.getNode(),
                        itpfFactory.createAnd(worker.getResult()));
                    nodeProofs.add(ruleWorker.getProof());
                }
            }
        }

        if (newEdgeFormulas.isEmpty() && newNodeFormulas.isEmpty()) {
            return ResultFactory.unsuccessful();
        } else {
            final Proof proof =
                new ItpfSchedulerGraphProof("ItpfSchedulerGraphProcessor",
                    ImmutableCreator.create(nodeProofs),
                    ImmutableCreator.create(edgeProofs));

            IDependencyGraph newGraph = null;
            try {
                newGraph =
                    idp.getIdpGraph().change(
                        newNodeFormulas,
                        newEdgeFormulas.getMap(),
                        null,
                        null,
                        null,
                        this.mark);
            } catch (final AssertionError e) {
                if (Globals.DEBUG_MPLUECKER) {
                    System.err.println(proof);
                }
                throw e;
            }

            final Set<Mark<?>> usedMarks = new HashSet<Mark<?>>();
            final Set<GenericItpfRule<?>> allRules = this.strategy.getAllRules();
            for (final GenericItpfRule<?> rule : allRules) {
                usedMarks.addAll(rule.getUsedMarks());
            }

            final YNMImplication direction;
            if (sound) {
                if (complete) {
                    direction = YNMImplication.EQUIVALENT;
                } else {
                    direction = YNMImplication.SOUND;
                }
            } else {
                if (complete) {
                    direction = YNMImplication.COMPLETE;
                } else {
                    direction = YNMImplication.ANTIVALENT;
                }
            }

            return ResultFactory.proved(
                idp.change(newGraph,
                    ImmutableCreator.create(GraphUtil.cleanupSubGraphs(GraphUtil.cleanupRemovedEdges(newGraph, idp.getSubGraphs())))),
                direction, proof);
        }
    }

}
