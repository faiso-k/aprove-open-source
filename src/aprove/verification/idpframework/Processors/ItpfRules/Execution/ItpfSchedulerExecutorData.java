package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;

/**
 *
 * @author MP
 */
public class ItpfSchedulerExecutorData extends SchedulerExecutorData<Itpf, GenericItpfRule<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> {

    protected final Itpf formula;

    public ItpfSchedulerExecutorData(final IDPProblem idp,
            final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy,
            final ImplicationType executionRequirements,
            final Itpf formula,
            final Abortion aborter) {
        super(idp, strategy, executionRequirements, new ItpfSchedulerProof<Itpf, GenericItpfRule<?>>(idp,
            formula, idp.getItpfFactory().createTrue()), aborter);
        this.formula = formula;
    }

    public Itpf getFormula() {
        return this.formula;
    }

    @Override
    public boolean isFormulaData() {
        return true;
    }

}
