package aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class IDPSequence<FormulaType extends ProcessableFormula, RuleType extends ExecutableRule<FormulaType, ?>> implements IDPSchedulerStrategy<FormulaType, RuleType> {

    private final ImmutableList<IDPSchedulerStrategy<FormulaType, RuleType>> strategies;

    public IDPSequence(final ImmutableList<IDPSchedulerStrategy<FormulaType, RuleType>> strategies) {
        this.strategies = strategies;
    }

    @Override
    public Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>> apply(final ItpfSchedulerProof<FormulaType, RuleType> proof,
        final ImplicationType executionRequirements,
        final Abortion aborter) throws AbortionException {
        for (final IDPSchedulerStrategy<FormulaType, RuleType> strategy : this.strategies) {
            Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>> result = new Pair<Boolean, IDPSchedulerStrategy<FormulaType,RuleType>>(true, strategy);
            do {
                result = result.y.apply(proof, executionRequirements, aborter);
            } while (result.x && result.y != null);

            if (!result.x) {
                return new Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>>(false, null);
            }
        }
        return new Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>>(true, null);
    }

    @Override
    public Set<RuleType> getAllRules() {
        final Set<RuleType> res = new LinkedHashSet<RuleType>();

        for (final IDPSchedulerStrategy<FormulaType, RuleType> strategy : this.strategies) {
            res.addAll(strategy.getAllRules());
        }

        return res;
    }


}
