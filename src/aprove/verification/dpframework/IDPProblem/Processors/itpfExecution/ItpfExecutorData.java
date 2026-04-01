package aprove.verification.dpframework.IDPProblem.Processors.itpfExecution;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.itpf.IItpfRule.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 *
 * @author mpluecke
 */
public class ItpfExecutorData implements AbortableRunnable {

    private IDPProblem idp;
    private Itpf formula;
    private IItpfRule rule;
    private ApplicationMode mode;
    private Itpf result;

    public ItpfExecutorData(IDPProblem idp, IItpfRule rule, Itpf formula, IItpfRule.ApplicationMode mode) {
        this.idp = idp;
        this.rule = rule;
        this.formula = formula;
        this.mode = mode;
    }

    //@Override
    @Override
    public WorkStatus execute(Abortion aborter) throws AbortionException {
        this.result = this.formula;
        if (this.rule.isApplicable(this.idp, this.formula, this.mode)) {
            Itpf result = this.rule.process(this.idp, this.formula, this.mode, aborter);
            if (Globals.useAssertions) {
                // see definition if ITPF-rule
                assert(this.formula.getFreeVariables().containsAll(result.getFreeVariables()));
            }
            // Don't set the field until the assertion checks out
            this.result = result;
        }
        return WorkStatus.CONTINUE;
    }

    public Itpf getResult() {
        return this.result;
    }
}
