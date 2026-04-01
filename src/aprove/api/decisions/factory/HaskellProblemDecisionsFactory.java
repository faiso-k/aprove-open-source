package aprove.api.decisions.factory;

import java.util.*;

import aprove.api.decisions.*;
import aprove.api.decisions.impl.*;
import aprove.api.decisions.results.*;
import aprove.api.impl.*;

public enum HaskellProblemDecisionsFactory {
    ;

    public static Optional<ProblemDecisions>
           create(ProblemInputImpl problemInput) throws ProblemDecisionsInstantiationException {
        return ProblemDecisionsImpl.create(new AnalyzableProblemInputCreator(problemInput,
                                                                     HaskellProblemDecisionsFactory::belongsToProtoAnnotation,
                                                                     HaskellProblemDecisionsFactory::toProtoAnnotation),
                                           Optional.empty(),
                                           Optional.empty(),
                                           Optional.empty(),
                                           Optional.of(new QueryDecisionImpl()));
    }

    private static boolean belongsToProtoAnnotation(String line) {
        return line.trim().matches("\\{-#\\s?htermination\\s?\\([^\\)]*\\)\\s?#-\\}");
    }

    private static String toProtoAnnotation(ProblemDecisionResults problemDecisionResults) {
        return problemDecisionResults.getQuery();
    }
}
