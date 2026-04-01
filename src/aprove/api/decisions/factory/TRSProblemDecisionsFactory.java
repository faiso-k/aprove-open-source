package aprove.api.decisions.factory;

import java.util.*;

import aprove.api.decisions.*;
import aprove.api.decisions.impl.*;
import aprove.api.decisions.results.*;
import aprove.api.impl.*;

public enum TRSProblemDecisionsFactory {
    ;

    private static final Set<HandlingMode> HANDLING_MODES = createHandlingModes();

    private static Set<HandlingMode> createHandlingModes() {
        Set<HandlingMode> result = new LinkedHashSet<>();
        result.add(HandlingMode.TERMINATION);
        result.add(HandlingMode.RUNTIME_COMPLEXITY);
        return result;
    }

    public static Optional<ProblemDecisions>
           create(ProblemInputImpl problemInput) throws ProblemDecisionsInstantiationException {
        return ProblemDecisionsImpl.create(new AnalyzableProblemInputCreator(problemInput,
                                                                     TRSProblemDecisionsFactory::belongsToProtoAnnotation,
                                                                     TRSProblemDecisionsFactory::toProtoAnnotation),
                                           Optional.of(HandlingModeDecisionImpl.create(HandlingMode.TERMINATION,
                                                                                       HANDLING_MODES)),
                                           Optional.of(EvaluationStrategyDecisionImpl.create(EvaluationStrategy.INNERMOST,
                                                                                             Arrays.asList(EvaluationStrategy.INNERMOST,
                                                                                                           EvaluationStrategy.FULL))),
                                           Optional.empty(),
                                           Optional.empty());
    }

    private static boolean belongsToProtoAnnotation(String line) {
        return line.trim().toUpperCase().startsWith("(GOAL ");
    }

    private static String toProtoAnnotation(ProblemDecisionResults problemDecisionResults) {
        Optional<String> goal = getGoal(problemDecisionResults.getHandlingMode());
        Optional<String> strategy = getStrategy(problemDecisionResults.getEvaluationStrategy());
        if (goal.isPresent() && strategy.isPresent()) {
            return goal.get() + strategy.get();
        } else {
            throw new IllegalArgumentException("the passed decision results are not compatible with the available choices");
        }
    }

    private static Optional<String> getGoal(HandlingMode handlingMode) {
        switch (handlingMode) {
            case TERMINATION:
                return Optional.of("GOAL TERMINATION,");
            case RUNTIME_COMPLEXITY:
                return Optional.of("GOAL COMPLEXITY,");
            default:
                assert false;
                return Optional.empty();
        }
    }

    private static Optional<String> getStrategy(EvaluationStrategy evaluationStrategy) {
        switch (evaluationStrategy) {
            case INNERMOST:
                return Optional.of("STRATEGY INNERMOST");
            case FULL:
                return Optional.of("STRATEGY FULL");
            default:
                assert false;
                return Optional.empty();
        }
    }
}
