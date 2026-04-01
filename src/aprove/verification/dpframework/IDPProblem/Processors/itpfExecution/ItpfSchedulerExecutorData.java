package aprove.verification.dpframework.IDPProblem.Processors.itpfExecution;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.itpf.IItpfRule.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public abstract class ItpfSchedulerExecutorData<ProofType extends ItpfSchedulerProof> implements AbortableRunnable {

    protected final IDPProblem idp;
    protected final ImmutableList<IItpfRule> rules;
    protected final ApplicationMode mode;
    protected final Abortion aborter;
    protected final Map<IItpfRule, Set<IItpfRule>> ruleGrouping;
    protected Itpf result;
    protected ProofType proof;

    public ItpfSchedulerExecutorData(IDPProblem idp,
            ImmutableList<IItpfRule> rules,
            Map<IItpfRule, Set<IItpfRule>> ruleGrouping,
            IItpfRule.ApplicationMode mode, Abortion aborter) {
        this.idp = idp;
        this.rules = rules;
        this.ruleGrouping = ruleGrouping;
        this.mode = mode;
        this.aborter = aborter;
    }

    @Override
    public WorkStatus execute(Abortion aborter) {
        if (this.result != null) {
            assert (false) : "only run once";
        }
        this.proof = this.createInitialProof();
        this.result = this.getInitialFormula();
        Itpf oldResult;
        outer: do {
            oldResult = this.result;
            ruleFor: for (IItpfRule rule : this.rules) {
                if (rule.isApplicable(this.idp, oldResult, this.mode)) {
                    try {
                        this.result = rule.process(this.idp, oldResult, this.mode, aborter);
                        if (oldResult != this.result) {
                            if (Globals.useAssertions) {
                                // see definition if ITPF-rule
                                assert (oldResult.getFreeVariables()
                                        .containsAll(this.result.getFreeVariables()));
                            }
                            this.proof.addStep(rule, this.result);
                            break ruleFor;
                        }
                    } catch (AbortionException e) {
                        break outer;
                    }
                }
            }
            try {
                aborter.checkAbortion();
            } catch (AbortionException e) {
                break;
            }
        } while (oldResult != this.result);
        // return ResultType.FAILED;
        return WorkStatus.CONTINUE;
    }

    protected abstract ProofType createInitialProof();

    protected abstract Itpf getInitialFormula();

    public ProofType getProof() {
        return this.proof;
    }
}
