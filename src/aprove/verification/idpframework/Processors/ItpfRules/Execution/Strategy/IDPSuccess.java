package aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author MP
 */
public class IDPSuccess<FormulaType extends ProcessableFormula, RuleType extends ExecutableRule<FormulaType, ?>> implements IDPSchedulerStrategy<FormulaType, RuleType> {

    private final IDPSchedulerStrategy<FormulaType, RuleType> strategy;

    public IDPSuccess(final IDPSchedulerStrategy<FormulaType, RuleType> strategy) {
        this.strategy = strategy;
    }

    @Override
    public Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>> apply(final ItpfSchedulerProof<FormulaType, RuleType> proof,
        final ImplicationType executionRequirements,
        final Abortion aborter) throws AbortionException {

        Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>> strategyResult = new Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>>(true, this.strategy);

        do {
            strategyResult =
                strategyResult.y.apply(proof, executionRequirements, aborter);

            if (strategyResult.y instanceof IDPSuccess) {
                strategyResult.x = true;
                strategyResult.y = ((IDPSuccess<FormulaType, RuleType>)strategyResult.y).strategy;
            }
        } while (strategyResult.x && strategyResult.y != null);

        strategyResult.x = true;

        return strategyResult;
    }

    @Override
    public Set<RuleType> getAllRules() {
        return this.strategy.getAllRules();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime * result + ((this.strategy == null) ? 0 : this.strategy.hashCode());
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final IDPSuccess<?, ?> other = (IDPSuccess<?, ?>) obj;
        if (this.strategy == null) {
            if (other.strategy != null) {
                return false;
            }
        } else if (!this.strategy.equals(other.strategy)) {
            return false;
        }
        return true;
    }


}
