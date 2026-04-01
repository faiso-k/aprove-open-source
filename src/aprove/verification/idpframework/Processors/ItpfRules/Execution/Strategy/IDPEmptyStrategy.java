package aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author MP
 */
public class IDPEmptyStrategy<FormulaType extends ProcessableFormula, RuleType extends ExecutableRule<FormulaType, ?>> implements IDPSchedulerStrategy<FormulaType, RuleType> {


    public IDPEmptyStrategy() {
    }


    @Override
    public Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>> apply(final ItpfSchedulerProof<FormulaType, RuleType> proof,
        final ImplicationType executionRequirements,
        final Abortion aborter) throws AbortionException {

        return new Pair<Boolean, IDPSchedulerStrategy<FormulaType,RuleType>>(true, null);
    }

    @Override
    public Set<RuleType> getAllRules() {
        return Collections.emptySet();
    }

    @Override
    public int hashCode() {
        return 37;
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
        return true;
    }

}
