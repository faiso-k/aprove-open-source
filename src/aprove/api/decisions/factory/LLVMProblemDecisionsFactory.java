package aprove.api.decisions.factory;

import java.util.*;

import aprove.api.decisions.*;
import aprove.api.decisions.impl.*;
import aprove.api.decisions.results.*;
import aprove.api.impl.*;

public enum LLVMProblemDecisionsFactory {
    ;

    private static final Map<HandlingMode, String> HANDLING_MODES = createHandlingModes();

    private static Map<HandlingMode, String> createHandlingModes() {
        Map<HandlingMode, String> result = new LinkedHashMap<>();
        result.put(HandlingMode.TERMINATION, ";query:");
        result.put(HandlingMode.MEMORY_SAFETY, ";safety:");
        return result;
    }

    public static Optional<ProblemDecisions>
           create(ProblemInputImpl problemInput) throws ProblemDecisionsInstantiationException {
        return ProblemDecisionsImpl.create(new AnalyzableProblemInputCreator(problemInput,
                                                                     LLVMProblemDecisionsFactory::belongsToProtoAnnotation,
                                                                     LLVMProblemDecisionsFactory::toProtoAnnotation),
                                           Optional.of(HandlingModeDecisionImpl.create(HandlingMode.TERMINATION,
                                                                                       HANDLING_MODES.keySet())),
                                           Optional.empty(),
                                           Optional.empty(),
                                           Optional.of(new QueryDecisionImpl()));
    }

    private static boolean belongsToProtoAnnotation(String str) {
        String input = str.replaceAll(" ", "");
        return HANDLING_MODES.values().stream().filter(keyword -> input.startsWith(keyword)).findAny().isPresent();
    }

    private static String toProtoAnnotation(ProblemDecisionResults problemDecisionResults) {
        return HANDLING_MODES.get(problemDecisionResults.getHandlingMode()) + problemDecisionResults.getQuery();
    }
}
