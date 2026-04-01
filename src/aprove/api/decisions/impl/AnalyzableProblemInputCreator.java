package aprove.api.decisions.impl;

import java.io.*;
import java.util.function.*;

import aprove.api.*;
import aprove.api.decisions.results.*;
import aprove.api.impl.*;

public class AnalyzableProblemInputCreator {

    private final ProblemInputImpl problemInput;
    private final Predicate<String> lineBelongsToProtoAnnotationTester;
    private final Function<ProblemDecisionResults, String> protoAnnotationCreator;

    public AnalyzableProblemInputCreator(ProblemInputImpl problemInput,
                                         Predicate<String> lineBelongsToProtoAnnotationTester,
                                         Function<ProblemDecisionResults, String> protoAnnotationCreator) {
        this.problemInput = problemInput;
        this.lineBelongsToProtoAnnotationTester = lineBelongsToProtoAnnotationTester;
        this.protoAnnotationCreator = protoAnnotationCreator;
    }

    public boolean containsProtoAnnotation() throws IOException {
        try {
            return problemInput.lines()
                               .map(String::trim)
                               .filter(lineBelongsToProtoAnnotationTester)
                               .findAny()
                               .isPresent();
        } catch (UncheckedIOException e) {
            throw e.getCause();
        }
    }

    public AnalyzableProblemInput createAnalyzableProblemInput(ProblemDecisionResults problemDecisionResults) {
        return problemInput.withAnnotation(protoAnnotationCreator.apply(problemDecisionResults));
    }
}
