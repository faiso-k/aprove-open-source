package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;

import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;
import aprove.verification.idpframework.Processors.ItpfRules.poly.*;
import aprove.verification.idpframework.Processors.NonInf.ItpfRules.*;
import aprove.verification.idpframework.Processors.Poly.*;
import immutables.*;

/**
 * @author MP
 */
public enum ItpfStrategy {

    HIDDEN_SIMPLIFICATION {
        @Override
        public IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> sequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
            ItpfStrategy.addToSequence(sequence, new ItpfStepDetect(),
                ApplicationMode.Multistep, true);
            ItpfStrategy.addToSequence(sequence, new ItpfUnify(), ApplicationMode.Multistep,
                true);
            ItpfStrategy.addToSequence(sequence, new ItpfRootConstr(),
                ApplicationMode.Multistep, true);

            return new IDPSequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(sequence));
        }
    },

    PREPARE_QDP {

        @Override
        protected IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {

            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> sequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            ItpfStrategy.addToSequence(sequence, HIDDEN_SIMPLIFICATION.getStrategy(), false);

//            addToSequence(sequence, new ItpfRewriteTransitivity(),
//                ApplicationMode.Multistep, false);
            ItpfStrategy.addToSequence(sequence, new PolyRuleRelOpToPoly(true),
                ApplicationMode.Multistep, false);
            ItpfStrategy.addToSequence(sequence, new PolyRuleExpandNeq(),
                ApplicationMode.Multistep, false);

            return new IDPAnySequence<Itpf, GenericItpfRule<?>>(
                    ImmutableCreator.create(sequence));
        }

    },

    REMOVE_CONSTRUCTORS {
        @Override
        protected IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> sequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
            ItpfStrategy.addToSequence(sequence, new ItpfRootConstr(),
                ApplicationMode.Multistep, false);
            ItpfStrategy.addToSequence(sequence, new ItpfBoolOp(),
                ApplicationMode.Multistep, false);

            return new IDPAnySequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(sequence));
        }
    },

    TO_BIGINT_POLY {
        @Override
        protected IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> polySequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            ItpfStrategy.addToSequence(polySequence, new PolyRuleRelOpToPoly(false),
                ApplicationMode.Multistep, false);
            ItpfStrategy.addToSequence(polySequence, new PolyRuleArithmeticToPoly(false),
                ApplicationMode.Multistep, false);
            ItpfStrategy.addToSequence(polySequence, new PolyRuleGCD(),
                ApplicationMode.Multistep, false);

            ItpfStrategy.addToSequence(polySequence,
                new PolyRuleConstraintRefinement<BigInt>(
                    new PolyRelationsEngine<BigInt>(), false),
                ApplicationMode.Multistep, false);

            return new IDPAnySequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(polySequence));
        }
    },

    KNOWLEDGE_GENERATION {
        @Override
        public IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> sequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            {
                final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> first =
                    new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
                ItpfStrategy.addToSequence(first, REMOVE_CONSTRUCTORS.getStrategy(), false);
                ItpfStrategy.addToSequence(first,
                    new ItpfStepDetect(),
                    ApplicationMode.Multistep, false);
                ItpfStrategy.addToSequence(first,
                    new ItpfUnify(),
                    ApplicationMode.Multistep, false);
                ItpfStrategy.addToSequence(first,
                    new ItpfRewriting(),
                    ApplicationMode.Multistep, false);
                ItpfStrategy.addToSequence(first,
                    new ItpfRelOp(),
                    ApplicationMode.Multistep, false);
                ItpfStrategy.addToSequence(first,
                    new ItpfVarReduct(),
                    ApplicationMode.Multistep, false);
                ItpfStrategy.addToSequence(sequence, new IDPFirst<Itpf, GenericItpfRule<?>>(
                    ImmutableCreator.create(first), -1),  false);
            }

            ItpfStrategy.addToSequence(sequence, TO_BIGINT_POLY.getStrategy(), false);

//            addToSequence(sequence, new ItpfRewriteTransitivity(),
//                ApplicationMode.Multistep, false);

            ItpfStrategy.addToSequence(sequence, new ItpfRuleDropFreeVariables(false),
                ApplicationMode.Multistep,  false);

            return new IDPAnySequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(sequence));
        }
    },

    BigIntPolyConstraintsStrategy {

        @Override
        protected IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> polySequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            ItpfStrategy.addToSequence(polySequence, new ItpfStepDetect(),
                ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence, new ItpRuleExpandDivModulo(),
                ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence, TO_BIGINT_POLY.getStrategy(), true);

            ItpfStrategy.addToSequence(polySequence, new PolyRuleReachabilityToPoly(),
                ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence, new PolyRuleDropNonPoly(),
                ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence,
                new PolyRuleConstraintRefinement<BigInt>(
                    new PolyRelationsEngine<BigInt>(), true),
                ApplicationMode.Multistep, true);


            {
                final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> polyFirst =
                    new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
                ItpfStrategy.addToSequence(polyFirst, new PolyRuleGtNormalization(),
                    ApplicationMode.Multistep, false);

                ItpfStrategy.addToSequence(polyFirst, new ItpfTrivialImplication(),
                    ApplicationMode.Multistep, false);

                ItpfStrategy.addToSequence(polyFirst, new ItpfImplicationCompression(),
                    ApplicationMode.Multistep, false);
                ItpfStrategy.addToSequence(polyFirst, new ItpfImplicationSplit<BigInt>(),
                    ApplicationMode.Multistep, false);
                ItpfStrategy.addToSequence(polyFirst, new ItpfSplitToSubFormulas(),
                    ApplicationMode.Multistep, false);

                ItpfStrategy.addToSequence(polyFirst, new ItpfExtractSideConstraints(),
                    ApplicationMode.Multistep, false);
                ItpfStrategy.addToSequence(polyFirst, new PolyRuleGCD(),
                    ApplicationMode.Multistep, false);

                ItpfStrategy.addToSequence(polyFirst,
                    new PolyRuleMultiplyPolyVarPrecondition(),
                    ApplicationMode.Multistep, false);

                ItpfStrategy.addToSequence(polyFirst, new ItpfRuleSolveTrivialConclusion(),
                    ApplicationMode.Multistep, false);

                ItpfStrategy.addToSequence(polyFirst, new PolyRuleExpandNeq(),
                    ApplicationMode.Multistep, false);
//                addToSequence(polyFirst, new RuleExtractPrecondition(),
//                    ApplicationMode.Multistep, false);

                ItpfStrategy.addToSequence(polySequence, new IDPFirst<Itpf, GenericItpfRule<?>>(
                    ImmutableCreator.create(polyFirst), -1), true);
            }

            ItpfStrategy.addToSequence(polySequence,
                new PolyRuleConstraintRefinement<BigInt>(
                    new PolyRelationsEngine<BigInt>(), false),
                ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence, new PolyRuleInstatiation<BigInt>(
                    new BigIntSMTEngine()), ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence, new PolyRuleAbstractRelToPoly(),
                ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence, new PolyRuleMaxRemoval<BigInt>(),
                ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence, new PolyRuleIntroduceNatConditions(), ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence,
                new PolyRuleConstraintRefinement<BigInt>(
                    new PolyRelationsEngine<BigInt>(), false),
                ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence,
                new PolyRuleMultiplyPolyVarPrecondition(),
                ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence, new ItpfDropUnusedVarsPrecondition(),
                ApplicationMode.Multistep, true);

            ItpfStrategy.addToSequence(polySequence,
                new PolyRuleConditionalToUnconditional<BigInt>(),
                ApplicationMode.Multistep, true);
            ItpfStrategy.addToSequence(polySequence, new PolyRuleDiophantine(),
                ApplicationMode.Multistep, true);
            ItpfStrategy.addToSequence(polySequence, new ItpfDropPreconditions(),
                ApplicationMode.Multistep, true);
            ItpfStrategy.addToSequence(polySequence, new ItpfTrivialImplication(),
                ApplicationMode.Multistep, true);
            ItpfStrategy.addToSequence(polySequence, new PolyRuleSolveBoundConstraints(),
                ApplicationMode.Multistep, true);

            return new IDPSequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(polySequence));
        }

    },

    DefaultStrategy {
        @Override
        public IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {

            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> strategySequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            ItpfStrategy.addToSequence(strategySequence, KNOWLEDGE_GENERATION.getStrategy(),
                true);

            // Poly strategy
            {
                strategySequence.add(BigIntPolyConstraintsStrategy.getStrategy());
            }

            return new IDPSequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(strategySequence));
        }
    };

    private final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy;

    private ItpfStrategy() {
        this.strategy = this.createStrategy();
    }

    public final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> getStrategy() {
        return this.strategy;
    }

    protected abstract IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy();

    public static <FormulaType extends ProcessableFormula, RuleType extends ExecutableRule<FormulaType, ?>> void addToSequence(final List<IDPSchedulerStrategy<FormulaType, RuleType>> sequence,
        final RuleType rule,
        final ApplicationMode applicationMode,
        final boolean wrapSuccess) {
        final IDPRuleApplication<FormulaType, RuleType> ruleApplication =
            new IDPRuleApplication<FormulaType, RuleType>(rule, applicationMode);

        if (wrapSuccess) {
            sequence.add(new IDPSuccess<FormulaType, RuleType>(ruleApplication));
        } else {
            sequence.add(ruleApplication);
        }
    }

    public static <FormulaType extends ProcessableFormula, RuleType extends ExecutableRule<FormulaType, ?>> void addToSequence(final List<IDPSchedulerStrategy<FormulaType, RuleType>> sequence,
        final IDPSchedulerStrategy<FormulaType, RuleType> strategy,
        final boolean wrapSuccess) {
        if (wrapSuccess) {
            sequence.add(new IDPSuccess<FormulaType, RuleType>(strategy));
        } else {
            sequence.add(strategy);
        }
    }

}
