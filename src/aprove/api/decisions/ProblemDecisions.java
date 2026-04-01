package aprove.api.decisions;

import java.util.*;

import aprove.api.*;

/**
 * Represents missing information that needs to be supplied to actually analyze a given {@link ProblemInput}.
 * Depending on the given problem, different decisions need to be made.
 * If a decision is empty, the given problem does not require the decision to be made.
 */
public interface ProblemDecisions {

    Optional<HandlingModeDecision> getHandlingModeDecision();

    Optional<EvaluationStrategyDecision> getEvaluationStrategyDecision();

    Optional<SymbolDecision> getSymbolDecision();

    Optional<SymbolModingDecision> getSymbolModingDecision();

    Optional<QueryDecision> getQueryDecision();

    ProblemDecisionMaker getProblemDecisionMaker();
}
