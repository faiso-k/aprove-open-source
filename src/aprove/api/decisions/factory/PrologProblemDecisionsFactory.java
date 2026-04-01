package aprove.api.decisions.factory;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.stream.*;

import aprove.api.decisions.*;
import aprove.api.decisions.impl.*;
import aprove.api.decisions.impl.HandlingMode;
import aprove.api.decisions.results.*;
import aprove.api.impl.*;
import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.Translator;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;

public enum PrologProblemDecisionsFactory {
    ;

    private static final Map<HandlingMode, String> HANDLING_MODES = createHandlingModes();

    private static Map<HandlingMode, String> createHandlingModes() {
        Map<HandlingMode, String> result = new LinkedHashMap<>();
        result.put(HandlingMode.TERMINATION, "%query");
        result.put(HandlingMode.RUNTIME_COMPLEXITY, "%complexity");
        result.put(HandlingMode.DETERMINACY, "%determinacy");
        return result;
    }

    public static Optional<ProblemDecisions>
           create(ProblemInputImpl problemInput) throws ProblemDecisionsInstantiationException {
        return ProblemDecisionsImpl.create(new AnalyzableProblemInputCreator(problemInput,
                                                                     PrologProblemDecisionsFactory::belongsToProtoAnnotation,
                                                                     PrologProblemDecisionsFactory::toProtoAnnotation),
                                           Optional.of(HandlingModeDecisionImpl.create(HandlingMode.TERMINATION,
                                                                                       HANDLING_MODES.keySet())),
                                           Optional.empty(),
                                           Optional.of(SymbolDecisionImpl.createWithModing(loadSymbols(problemInput.getPath()))),
                                           Optional.empty());
    }

    private static Set<FunctionSymbol> loadSymbols(Path problemPath) throws ProblemDecisionsInstantiationException {
        try {
            Translator prologTranslator = new Translator();
            prologTranslator.translate(problemPath.toFile());
            return prologTranslator.getProgram().createSetOfDefinedPredicates();
        } catch (FileNotFoundException | TranslationException | PrologSyntaxException e) {
            e.printStackTrace();
            throw new ProblemDecisionsInstantiationException("Parsing failed!", e);
        }
    }

    private static boolean belongsToProtoAnnotation(String line) {
        String input = line.trim();
        return HANDLING_MODES.values().stream().filter(keyword -> input.startsWith(keyword)).findAny().isPresent();
    }

    private static String toProtoAnnotation(ProblemDecisionResults problemDecisionResults) {
        return HANDLING_MODES.get(problemDecisionResults.getHandlingMode())
               + ": "
               + problemDecisionResults.getSymbol()
               + "("
               + problemDecisionResults.getSymbolModing()
                                       .stream()
                                       .map(b -> b ? "i" : "o")
                                       .collect(Collectors.joining(","))
               + ")";
    }
}
