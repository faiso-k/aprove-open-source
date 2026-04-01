package aprove.api.decisions.impl;

import java.util.*;
import java.util.function.*;

import aprove.api.*;
import aprove.api.decisions.*;
import aprove.api.decisions.ProblemDecisionMaker.*;

public class ProblemDecisionMakerImpl implements
                                      ProblemDecisionMaker,
                                      BeforeEvaluationStrategy,
                                      BeforeSymbol,
                                      BeforeSymbolModing,
                                      BeforeQuery,
                                      BeforeConstruct {

    private final AnalyzableProblemInputCreator problemInputAnnotator;
    private final ProblemDecisionsImpl problemDecisions;

    private Supplier<String> handlingModeDecider;
    private Supplier<String> evaluationStrategyDecider;
    private Supplier<String> symbolDecider;
    private Supplier<List<Boolean>> symbolModingDecider;
    private Supplier<String> queryDecider;

    public ProblemDecisionMakerImpl(AnalyzableProblemInputCreator problemInputAnnotator,
                                    ProblemDecisionsImpl problemDecisions) {
        this.problemInputAnnotator = problemInputAnnotator;
        this.problemDecisions = problemDecisions;
    }

    @Override
    public BeforeEvaluationStrategy decideHandlingMode(Supplier<String> decider) {
        Objects.requireNonNull(decider);
        this.handlingModeDecider = decider;
        return this;
    }

    @Override
    public BeforeSymbol decideEvaluationStrategy(Supplier<String> decider) {
        Objects.requireNonNull(decider);
        this.evaluationStrategyDecider = decider;
        return this;
    }

    @Override
    public BeforeSymbolModing decideSymbol(Supplier<String> decider) {
        Objects.requireNonNull(decider);
        this.symbolDecider = decider;
        return this;
    }

    @Override
    public BeforeQuery decideSymbolModing(Supplier<List<Boolean>> decider) {
        Objects.requireNonNull(decider);
        this.symbolModingDecider = decider;
        return this;
    }

    @Override
    public BeforeConstruct decideQuery(Supplier<String> decider) {
        Objects.requireNonNull(decider);
        this.queryDecider = decider;
        return this;
    }

    @Override
    public AnalyzableProblemInput construct() throws InvalidDecisionException {
        return problemInputAnnotator.createAnalyzableProblemInput(problemDecisions.createDecisionResults(handlingModeDecider,
                                                                                                        evaluationStrategyDecider,
                                                                                                        symbolDecider,
                                                                                                        symbolModingDecider,
                                                                                                        queryDecider));
    }
}
