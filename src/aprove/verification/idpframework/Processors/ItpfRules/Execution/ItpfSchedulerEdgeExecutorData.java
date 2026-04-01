package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;

/**
 * @author Martin Pluecker
 */
public class ItpfSchedulerEdgeExecutorData extends
        SchedulerExecutorData<Itpf, GenericItpfRule<?>, ItpfSchedulerEdgeProof> {

    protected final IEdge edge;
    protected final Itpf condition;

    public ItpfSchedulerEdgeExecutorData(final IDPProblem idp,
            final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy,
            final ImplicationType executionRequirements,
            final IEdge edge,
            final Itpf condition, final Abortion aborter) {
        super(idp, strategy, executionRequirements, new ItpfSchedulerEdgeProof(idp,
            edge, condition), aborter);
        this.edge = edge;
        this.condition = condition;
    }

    public IEdge getEdge() {
        return this.edge;
    }

    @Override
    public boolean isEdgeData() {
        return true;
    }

}
