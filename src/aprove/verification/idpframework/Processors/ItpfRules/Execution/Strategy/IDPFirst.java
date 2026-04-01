package aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class IDPFirst<FormulaType extends ProcessableFormula, RuleType extends ExecutableRule<FormulaType, ?>>
        implements IDPSchedulerStrategy<FormulaType, RuleType> {

    private final ImmutableList<? extends IDPSchedulerStrategy<FormulaType, RuleType>> strategies;
    private final int maxApplications;

    public IDPFirst(
            final ImmutableList<? extends IDPSchedulerStrategy<FormulaType, RuleType>> strategies,
            final int maxApplications) {
        this(strategies, maxApplications, true);
    }

    private IDPFirst(
        final ImmutableList<? extends IDPSchedulerStrategy<FormulaType, RuleType>> strategies,
        final int maxApplications,
        final boolean mustAssertStrategies) {
        this.strategies = strategies;
        if (mustAssertStrategies && Globals.useAssertions) {
            this.assertStrategies(strategies, maxApplications);
        }
        this.maxApplications = maxApplications;
    }

    private void assertStrategies(final ImmutableList<? extends IDPSchedulerStrategy<FormulaType, RuleType>> strategies, final int maxApplications) {
        for (final IDPSchedulerStrategy<FormulaType, RuleType> strategy : strategies) {
            assert maxApplications >= 0 || !(strategy instanceof IDPSuccess<?, ?>) : "do not add IDPSuccess to first";
        }
    }

    @Override
    public Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>> apply(final ItpfSchedulerProof<FormulaType, RuleType> proof,
        final ImplicationType executionRequirements,
        final Abortion aborter) throws AbortionException {
        for (final IDPSchedulerStrategy<FormulaType, RuleType> strategy : this.strategies) {

            Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>> result;
            do {
                result = strategy.apply(proof, executionRequirements, aborter);
            } while (result.y != null);

            if (result.x) {
                if (this.maxApplications >= 0 && this.maxApplications <= 1) {
                    return new Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>>(
                        true, null);
                } else {
                    return new Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>>(
                        true,
                        new IDPSuccess<FormulaType, RuleType>(
                            new IDPFirst<FormulaType, RuleType>(
                                    this.strategies,
                                    this.maxApplications > 0 ? this.maxApplications - 1 : -1,
                                    false)));
                }
            }
        }
        return new Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>>(
            false, null);
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
