package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;

/**
 * @author Martin Pluecker
 */
public class ItpfSchedulerVarExecutorData<C extends SemiRing<C>> extends
        SchedulerExecutorData<Itpf, GenericItpfRule<?>, ItpfSchedulerVarProof<C>> {

    protected final ItpfBoolPolyVar<C> var;

    public ItpfSchedulerVarExecutorData(final IDPProblem idp,
            final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy,
            final ImplicationType executionRequirements,
            final ItpfBoolPolyVar<C> var,
            final Itpf formula,
            final Abortion aborter) {
        super(idp, strategy, executionRequirements, new ItpfSchedulerVarProof<C>(idp,
            var, formula), aborter);
        this.var = var;
    }

    public ItpfBoolPolyVar<C> getVariable() {
        return this.var;
    }

    @Override
    public boolean isVarData() {
        return true;
    }

}
