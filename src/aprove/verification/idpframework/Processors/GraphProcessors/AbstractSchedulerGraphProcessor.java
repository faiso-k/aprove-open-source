package aprove.verification.idpframework.Processors.GraphProcessors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public abstract class AbstractSchedulerGraphProcessor<ResultType extends Result, ProblemType extends IDPProblem> extends
        AbstractGraphProcessor<ResultType, ProblemType> {

    protected final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy;

    protected AbstractSchedulerGraphProcessor(final String description,
            final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy) {
        super(description);
        if (strategy == null) {
            throw new IllegalArgumentException("strategy must not be null");
        }
        this.strategy = strategy;
    }

    @Override
    protected ResultType processIDPProblem(final ProblemType idp,
        final Abortion aborter) throws AbortionException {

        final List<SchedulerExecutorData<Itpf, GenericItpfRule<?>, ?>> workers =
            new ArrayList<SchedulerExecutorData<Itpf, GenericItpfRule<?>, ?>>(
                idp.getIdpGraph().getEdges().size());
        for (final Map.Entry<IEdge, Itpf> edgeCond : idp.getIdpGraph().getEdgeConditions().entrySet()) {
            assert edgeCond.getKey() != null;
            if (!edgeCond.getValue().isTrue()) {
                workers.add(new ItpfSchedulerEdgeExecutorData(idp, this.strategy, ImplicationType.SOUND,
                    edgeCond.getKey(), edgeCond.getValue(),
                    aborter));
            }
        }

        for (final Map.Entry<INode, Itpf> nodeCond : idp.getIdpGraph().getNodeConditions().entrySet()) {
            if (!nodeCond.getValue().isTrue()) {
                workers.add(new ItpfSchedulerNodeExecutorData(idp, this.strategy, ImplicationType.SOUND,
                    nodeCond.getKey(), nodeCond.getValue(),
                    aborter));
            }
        }

        MultithreadedExecutor.execute(workers, aborter);

        return this.processResult(idp, workers, aborter);

    }

    protected abstract ResultType processResult(ProblemType idp,
        List<SchedulerExecutorData<Itpf, GenericItpfRule<?>, ?>> workers,
        Abortion aborter);

    protected static class ItpfSchedulerGraphProof extends DefaultProof
            implements IDPExportable {

        protected final List<ItpfSchedulerNodeProof> ruleProofs;
        protected final List<ItpfSchedulerEdgeProof> edgeProofs;
        private final String description;

        public ItpfSchedulerGraphProof(final String description,
                final ImmutableList<ItpfSchedulerNodeProof> ruleProofs,
                final ImmutableList<ItpfSchedulerEdgeProof> edgeProofs) {
            this.description = description;
            this.ruleProofs = ruleProofs;
            this.edgeProofs = edgeProofs;
        }

        @Override
        public final String export(final Export_Util o) {
            return this.export(o, IDPExportable.DEFAULT_LEVEL);
        }

        @Override
        public final String export(final Export_Util o,
            final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            this.export(sb, o, level);
            return sb.toString();
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util o,
            final VerbosityLevel level) {
            sb.append(this.description);
            sb.append(o.linebreak());
            int nextEquationId = 0;

            for (final ItpfSchedulerNodeProof nodeProof : this.ruleProofs) {
                final Pair<Integer, Map<Itpf, Integer>> exportResult = nodeProof.export(sb, o, level, nextEquationId);
                nextEquationId = exportResult.x;
                sb.append(o.linebreak());
            }

            for (final ItpfSchedulerEdgeProof edgeProof : this.edgeProofs) {
                final Pair<Integer, Map<Itpf, Integer>> exportResult = edgeProof.export(sb, o, level, nextEquationId);
                nextEquationId = exportResult.x;
                sb.append(o.linebreak());
            }
        }

    }

}