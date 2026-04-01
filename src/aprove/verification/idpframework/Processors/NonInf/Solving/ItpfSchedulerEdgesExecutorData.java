package aprove.verification.idpframework.Processors.NonInf.Solving;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;

/**
 *
 * @author Martin Pluecker
 */
public class ItpfSchedulerEdgesExecutorData extends SchedulerExecutorData<Itpf, GenericItpfRule<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> {

    private final Collection<IEdge> edges;

    public ItpfSchedulerEdgesExecutorData(final IDPProblem idp,
            final Itpf formula,
            final Collection<IEdge> edges,
            final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy,
            final ImplicationType executionRequirements,
            final Abortion aborter) {
        super(idp, strategy, executionRequirements, new ItpfSchedulerProof<Itpf, GenericItpfRule<?>>(idp, formula, idp.getItpfFactory().createTrue()), aborter);
        this.edges = edges;
    }

    public Collection<IEdge> getEdges() {
        return this.edges;
    }

}
