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
public class ItpfSchedulerNodeExecutorData extends
        SchedulerExecutorData<Itpf, GenericItpfRule<?>, ItpfSchedulerNodeProof> {

    protected final INode node;

    public ItpfSchedulerNodeExecutorData(final IDPProblem idp,
            final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy,
            final ImplicationType executionRequirements,
            final INode node,
            final Itpf condition,
            final Abortion aborter) {
        super(idp, strategy, executionRequirements, new ItpfSchedulerNodeProof(idp,
            node, condition), aborter);
        this.node = node;
    }

    public INode getNode() {
        return this.node;
    }

    @Override
    public boolean isNodeData() {
        return true;
    }

}
