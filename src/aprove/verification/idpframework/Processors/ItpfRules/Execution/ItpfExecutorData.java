package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * @author mpluecke
 */
public class ItpfExecutorData implements AbortableRunnable {

    private final IDPProblem idp;
    private final Itpf formula;
    private final GenericItpfRule<?> rule;
    private final ImplicationType executionRequirements;
    private final ApplicationMode mode;
    private Itpf result;
    private ImplicationType implication;

    public ItpfExecutorData(final IDPProblem idp, final GenericItpfRule<?> rule,
            final Itpf formula, final ImplicationType executionRequirements, final ApplicationMode mode) {
        this.idp = idp;
        this.rule = rule;
        this.formula = formula;
        this.executionRequirements = executionRequirements;
        this.mode = mode;
    }

    //@Override
    @Override
    public WorkStatus execute(final Abortion aborter) throws AbortionException {
        this.result = this.getFormula();
        if (this.rule.isApplicable(this.idp, this.getFormula(), this.mode)) {
            final ExecutionResult<Conjunction<Itpf>, Itpf> results = this.rule.process(this.idp, this.getFormula(), this.executionRequirements, this.mode, aborter);
            final Itpf result = this.idp.getItpfFactory().createAnd(results.result.asCollection());
            if (Globals.useAssertions) {
                // see definition if ITPF-rule
                assert (this.getFormula().getFreeVariables().containsAll(result.getFreeVariables()));
            }
            // Don't set the field until the assertion checks out
            this.result = result;
            this.implication = results.implication;
        }
        return WorkStatus.CONTINUE;
    }

    public Itpf getResult() {
        return this.result;
    }

    public ImplicationType getImplication() {
        return this.implication;
    }

    public Itpf getFormula() {
        return this.formula;
    }

    public boolean hasChanges() {
        return this.getResult() != this.getFormula();
    }
}
