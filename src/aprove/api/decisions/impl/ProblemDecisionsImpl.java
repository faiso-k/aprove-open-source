package aprove.api.decisions.impl;

import java.io.*;
import java.util.*;
import java.util.function.*;

import aprove.api.decisions.*;
import aprove.api.decisions.results.*;

public class ProblemDecisionsImpl implements ProblemDecisions {

    public static Optional<ProblemDecisions> create(AnalyzableProblemInputCreator problemInputAnnotator,
                                                    Optional<HandlingModeDecisionImpl> handlingModeDecision,
                                                    Optional<EvaluationStrategyDecisionImpl> evaluationStrategyDecision,
                                                    Optional<SymbolDecisionImpl> symbolDecision,
                                                    Optional<QueryDecisionImpl> queryDecision) throws ProblemDecisionsInstantiationException {
        try {
            if ((handlingModeDecision.isPresent()
                 || evaluationStrategyDecision.isPresent()
                 || symbolDecision.isPresent()
                 || symbolDecision.flatMap(SymbolDecisionImpl::getModingDecision).isPresent()
                 || queryDecision.isPresent())
                && !problemInputAnnotator.containsProtoAnnotation()) {
                return Optional.of(new ProblemDecisionsImpl(problemInputAnnotator,
                                                            handlingModeDecision,
                                                            evaluationStrategyDecision,
                                                            symbolDecision,
                                                            queryDecision));
            } else {
                return Optional.empty();
            }
        } catch (IOException e) {
            throw new ProblemDecisionsInstantiationException("unable to read problem input", e);
        }
    }

    private final AnalyzableProblemInputCreator problemInputAnnotator;
    private final Optional<HandlingModeDecisionImpl> handlingModeDecision;
    private final Optional<EvaluationStrategyDecisionImpl> evaluationStrategyDecision;
    private final Optional<SymbolDecisionImpl> symbolDecision;
    private final Optional<QueryDecisionImpl> queryDecision;

    public ProblemDecisionsImpl(AnalyzableProblemInputCreator problemInputAnnotator,
                                Optional<HandlingModeDecisionImpl> handlingModeDecision,
                                Optional<EvaluationStrategyDecisionImpl> evaluationStrategyDecision,
                                Optional<SymbolDecisionImpl> symbolDecision,
                                Optional<QueryDecisionImpl> queryDecision) {
        this.problemInputAnnotator = problemInputAnnotator;
        this.handlingModeDecision = handlingModeDecision;
        this.evaluationStrategyDecision = evaluationStrategyDecision;
        this.symbolDecision = symbolDecision;
        this.queryDecision = queryDecision;
    }

    @Override
    public Optional<HandlingModeDecision> getHandlingModeDecision() {
        return handlingModeDecision.map(Function.identity());
    }

    @Override
    public Optional<EvaluationStrategyDecision> getEvaluationStrategyDecision() {
        return evaluationStrategyDecision.map(Function.identity());
    }

    @Override
    public Optional<SymbolDecision> getSymbolDecision() {
        return symbolDecision.map(Function.identity());
    }

    @Override
    public Optional<SymbolModingDecision> getSymbolModingDecision() {
        return symbolDecision.flatMap(SymbolDecisionImpl::getModingDecision).map(Function.identity());
    }

    @Override
    public Optional<QueryDecision> getQueryDecision() {
        return queryDecision.map(Function.identity());
    }

    @Override
    public ProblemDecisionMaker getProblemDecisionMaker() {
        return new ProblemDecisionMakerImpl(problemInputAnnotator, this);
    }

    public ProblemDecisionResults createDecisionResults(Supplier<String> handlingModeDecider,
                                                        Supplier<String> evaluationStrategyDecider,
                                                        Supplier<String> symbolDecider,
                                                        Supplier<List<Boolean>> symbolModingDecider,
                                                        Supplier<String> queryDecider) throws InvalidDecisionException {
        return new ProblemDecisionResults(handlingModeDecision.map(d -> d.makeDecision(handlingModeDecider.get())),
                                          evaluationStrategyDecision.map(d -> d.makeDecision(evaluationStrategyDecider.get())),
                                          symbolDecision.map(d -> d.makeDecision(symbolDecider.get())),
                                          symbolDecision.flatMap(SymbolDecisionImpl::getModingDecision)
                                                        .map(d -> d.makeDecision(symbolDecider.get(),
                                                                                 symbolModingDecider.get())),
                                          queryDecision.map(d -> d.makeDecision(queryDecider.get())));
    }
}
