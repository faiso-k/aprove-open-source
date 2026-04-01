package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * @author Martin Pluecker
 */
public abstract class SchedulerExecutorData<FormulaType extends ProcessableFormula, RuleType extends ExecutableRule<FormulaType, ?>, ProofType extends ItpfSchedulerProof<FormulaType, RuleType>>
implements AbortableRunnable {

    protected final IDPProblem idp;
    protected final IDPSchedulerStrategy<FormulaType, RuleType> strategy;
    protected final ImplicationType executionRequirements;
    protected final Abortion aborter;
    protected final ProofType proof;

    public SchedulerExecutorData(final IDPProblem idp,
        final IDPSchedulerStrategy<FormulaType, RuleType> strategy,
        final ImplicationType executionRequirements,
        final ProofType proof, final Abortion aborter) {
        this.idp = idp;
        this.strategy = strategy;
        this.executionRequirements = executionRequirements;
        this.aborter = aborter;
        this.proof = proof;
    }

    @Override
    public WorkStatus execute(final Abortion aborter) {
        if (!this.proof.isEmptyProof()) {
            assert (false) : "only run once";
        }
        IDPSchedulerStrategy<FormulaType, RuleType> currentStrategy = this.strategy;
        Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>> result;
        do {
            try {
                result = currentStrategy.apply(this.proof, this.executionRequirements, aborter);
            } catch (final AbortionException e) {
                break;
            }
            currentStrategy = result.y;
        } while (currentStrategy != null);
        return WorkStatus.CONTINUE;
    }

    public ProofType getProof() {
        return this.proof;
    }

    public FormulaType getStartFormula() {
        return this.proof.getStartFormula();
    }

    public Set<FormulaType> getResult() {
        return this.proof.getLastFormulaStates();
    }

    public boolean isNodeData() {
        return false;
    }

    public boolean isFormulaData() {
        return false;
    }

    public boolean isVarData() {
        return false;
    }

    public boolean isEdgeData() {
        return false;
    }

    public boolean isSuccessfull() {
        return !this.proof.isFailedProof();
    }
}
