package aprove.verification.complexity.CIdtProblem.Utility;

import java.util.*;

import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;
import aprove.verification.idpframework.Processors.ItpfRules.poly.*;
import aprove.verification.idpframework.Processors.Poly.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 * copied from MP
 */
public enum CNDStrategy {

    CND_HIDDEN_SIMPLIFICATION {
        @Override
        public IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> sequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
            CNDStrategy.addToSequence(sequence, new ItpfStepDetect(),
                ApplicationMode.Multistep, true);
            CNDStrategy.addToSequence(sequence, new ItpfUnify(), ApplicationMode.Multistep,
                true);
            CNDStrategy.addToSequence(sequence, new ItpfRootConstr(),
                ApplicationMode.Multistep, true);

            return new IDPSequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(sequence));
        }
    },

    CND_REMOVE_CONSTRUCTORS {
        @Override
        protected IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> sequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
            CNDStrategy.addToSequence(sequence, new ItpfRootConstr(),
                ApplicationMode.Multistep, false);
            CNDStrategy.addToSequence(sequence, new ItpfBoolOp(),
                ApplicationMode.Multistep, false);

            return new IDPAnySequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(sequence));
        }
    },

    CND_TO_BIGINT_POLY {
        @Override
        protected IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> polySequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            CNDStrategy.addToSequence(polySequence, new PolyRuleRelOpToPoly(false),
                ApplicationMode.Multistep, false);
            CNDStrategy.addToSequence(polySequence, new PolyRuleArithmeticToPoly(false),
                ApplicationMode.Multistep, false);
            CNDStrategy.addToSequence(polySequence, new PolyRuleGCD(),
                ApplicationMode.Multistep, false);

            CNDStrategy.addToSequence(polySequence,
                new PolyRuleConstraintRefinement<BigInt>(
                    new PolyRelationsEngine<BigInt>(), false),
                ApplicationMode.Multistep, false);

            return new IDPAnySequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(polySequence));
        }
    },

    CND_KNOWLEDGE_GENERATION {
        @Override
        public IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> sequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            {
                final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> first =
                    new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
                CNDStrategy.addToSequence(first, CND_REMOVE_CONSTRUCTORS.getStrategy(), false);
                CNDStrategy.addToSequence(first,
                    new ItpfStepDetect(),
                    ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first,
                    new ItpfUnify(),
                    ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first,
                    new ItpfRewriting(),
                    ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first,
                    new ItpfRelOp(),
                    ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first,
                    new ItpfVarReduct(),
                    ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(sequence, new IDPFirst<Itpf, GenericItpfRule<?>>(
                    ImmutableCreator.create(first), -1),  false);
            }

            CNDStrategy.addToSequence(sequence, CND_TO_BIGINT_POLY.getStrategy(), false);

//            addToSequence(sequence, new ItpfRewriteTransitivity(),
//                ApplicationMode.Multistep, false);

            CNDStrategy.addToSequence(sequence, new ItpfRuleDropFreeVariables(false),
                ApplicationMode.Multistep,  false);

            return new IDPAnySequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(sequence));
        }
    },

    CND_BigIntPolyConstraintsStrategy {

        @Override
        protected IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> polySequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            CNDStrategy.addToSequence(polySequence, new ItpfStepDetect(),
                ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(polySequence, new ItpRuleExpandDivModulo(),
                ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(polySequence, CND_TO_BIGINT_POLY.getStrategy(), true);

            CNDStrategy.addToSequence(polySequence, new PolyRuleReachabilityToPoly(),
                ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(polySequence, new PolyRuleDropNonPoly(),
                ApplicationMode.Multistep, true);

            /*addToSequence(polySequence, new PolyRuleMaxRemoval<BigInt>(),
                ApplicationMode.Multistep, true);*/

            CNDStrategy.addToSequence(polySequence,
                new PolyRuleConstraintRefinement<BigInt>(
                    new PolyRelationsEngine<BigInt>(), true),
                ApplicationMode.Multistep, true);


            {
                final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> polyFirst =
                    new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
                CNDStrategy.addToSequence(polyFirst, new PolyRuleGtNormalization(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new ItpfTrivialImplication(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new ItpfImplicationCompression(),
                    ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(polyFirst, new ItpfImplicationSplit<BigInt>(),
                    ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(polyFirst, new ItpfSplitToSubFormulas(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new ItpfExtractSideConstraints(),
                    ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(polyFirst, new PolyRuleGCD(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst,
                    new PolyRuleMultiplyPolyVarPrecondition(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new ItpfRuleSolveTrivialConclusion(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new PolyRuleExpandNeq(),
                    ApplicationMode.Multistep, false);
//                addToSequence(polyFirst, new RuleExtractPrecondition(),
//                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polySequence, new IDPFirst<Itpf, GenericItpfRule<?>>(
                    ImmutableCreator.create(polyFirst), -1), true);
            }

            CNDStrategy.addToSequence(polySequence, new PolyRuleInstatiation<BigInt>(
                new BigIntSMTEngine()), ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(polySequence,
                new PolyRuleConstraintRefinement<BigInt>(
                    new PolyRelationsEngine<BigInt>(), false),
                ApplicationMode.Multistep, true);



            CNDStrategy.addToSequence(polySequence, new PolyRuleAbstractRelToPoly(),
                ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(polySequence, new PolyRuleMaxRemoval<BigInt>(),
                ApplicationMode.Multistep, true);


            {
                final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> polyFirst =
                    new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
                CNDStrategy.addToSequence(polyFirst, new PolyRuleGtNormalization(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new ItpfTrivialImplication(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new ItpfImplicationCompression(),
                    ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(polyFirst, new ItpfImplicationSplit<BigInt>(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new ItpfSplitToSubFormulas(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new ItpfExtractSideConstraints(),
                    ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(polyFirst, new PolyRuleGCD(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst,
                    new PolyRuleMultiplyPolyVarPrecondition(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new ItpfRuleSolveTrivialConclusion(),
                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polyFirst, new PolyRuleExpandNeq(),
                    ApplicationMode.Multistep, false);
//                addToSequence(polyFirst, new RuleExtractPrecondition(),
//                    ApplicationMode.Multistep, false);

                CNDStrategy.addToSequence(polySequence, new IDPFirst<Itpf, GenericItpfRule<?>>(
                    ImmutableCreator.create(polyFirst), -1), true);
            }

            CNDStrategy.addToSequence(polySequence, new PolyRuleInstatiation<BigInt>(
                    new BigIntSMTEngine()), ApplicationMode.Multistep, true);


            CNDStrategy.addToSequence(polySequence, new PolyRuleIntroduceNatConditions(), ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(polySequence,
                new PolyRuleConstraintRefinement<BigInt>(
                    new PolyRelationsEngine<BigInt>(), false),
                ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(polySequence,
                new PolyRuleMultiplyPolyVarPrecondition(),
                ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(polySequence, new ItpfDropUnusedVarsPrecondition(),
                ApplicationMode.Multistep, true);


            CNDStrategy.addToSequence(polySequence,
                new PolyRuleConditionalToUnconditional<BigInt>(),
                ApplicationMode.Multistep, true);
            CNDStrategy.addToSequence(polySequence, new PolyRuleDiophantine(),
                ApplicationMode.Multistep, true);
            CNDStrategy.addToSequence(polySequence, new ItpfDropPreconditions(),
                ApplicationMode.Multistep, true);
            CNDStrategy.addToSequence(polySequence, new ItpfTrivialImplication(),
                ApplicationMode.Multistep, true);
            /*addToSequence(polySequence, new PolyRuleSolveBoundConstraints(),
                ApplicationMode.Multistep, true);*/

            return new IDPSequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(polySequence));
        }

    },

    CND_NON_POLY_SIMPLIFICATION {
        @Override
        public IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> strategySequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            CNDStrategy.addToSequence(strategySequence, CND_HIDDEN_SIMPLIFICATION.getStrategy(), false);
            //addToSequence(strategySequence, new ItpfRewriteTransitivity(),
             //   ApplicationMode.Multistep, false);

            {
                final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> first =
                    new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
                CNDStrategy.addToSequence(first, CND_REMOVE_CONSTRUCTORS.getStrategy(), false);
                CNDStrategy.addToSequence(first, new ItpfStepDetect(), ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first, new ItpfUnify(), ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first, new ItpfRewriting(), ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first, new ItpfRelOp(), ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first, new ItpfVarReduct(), ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(strategySequence, new IDPFirst<Itpf, GenericItpfRule<?>>(ImmutableCreator.create(first), -1),
                    false);
            }

            return new IDPAnySequence<Itpf, GenericItpfRule<?>>(
                    ImmutableCreator.create(strategySequence));
        }
    },

    CND_ProveFalseStrategy {
        @Override
        public IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {
            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> strategySequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            CNDStrategy.addToSequence(strategySequence, CND_HIDDEN_SIMPLIFICATION.getStrategy(), true);

            {
                final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> first =
                    new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();
                CNDStrategy.addToSequence(first, CND_REMOVE_CONSTRUCTORS.getStrategy(), false);
                CNDStrategy.addToSequence(first, new ItpfStepDetect(), ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first, new ItpfUnify(), ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first, new ItpfRewriting(), ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first, new ItpfRelOp(), ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(first, new ItpfVarReduct(), ApplicationMode.Multistep, false);
                CNDStrategy.addToSequence(strategySequence, new IDPFirst<Itpf, GenericItpfRule<?>>(ImmutableCreator.create(first), -1),
                    true);
            }

            CNDStrategy.addToSequence(strategySequence, new ItpfStepDetect(),
                ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(strategySequence, new ItpRuleExpandDivModulo(),
                ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(strategySequence, new PolyRuleRelOpToPoly(false), ApplicationMode.Multistep, true);
            CNDStrategy.addToSequence(strategySequence, new PolyRuleArithmeticToPoly(false), ApplicationMode.Multistep, true);
            CNDStrategy.addToSequence(strategySequence, new PolyRuleGCD(), ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(strategySequence, new PolyRuleReachabilityToPoly(),
                ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(strategySequence, new PolyRuleDropNonPoly(),
                ApplicationMode.Multistep, true);

            CNDStrategy.addToSequence(strategySequence,
                new PolyRuleConstraintRefinement<BigInt>(
                    new PolyRelationsEngine<BigInt>(), true),
                ApplicationMode.Multistep, true);

            return new IDPSequence<Itpf, GenericItpfRule<?>>(ImmutableCreator.create(strategySequence));
        }
    },

    CND_DefaultStrategy {
        @Override
        public IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> createStrategy() {

            final ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>> strategySequence =
                new ArrayList<IDPSchedulerStrategy<Itpf, GenericItpfRule<?>>>();

            CNDStrategy.addToSequence(strategySequence, CND_KNOWLEDGE_GENERATION.getStrategy(),
                true);

            // Poly strategy
            {
                strategySequence.add(CND_BigIntPolyConstraintsStrategy.getStrategy());
            }

            return new IDPSequence<Itpf, GenericItpfRule<?>>(
                ImmutableCreator.create(strategySequence));
        }
    };

    private final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy;

    private CNDStrategy() {
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
