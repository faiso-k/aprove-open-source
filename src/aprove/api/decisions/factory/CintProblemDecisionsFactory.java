package aprove.api.decisions.factory;

import java.io.*;
import java.nio.file.*;
import java.util.*;

import aprove.api.decisions.*;
import aprove.api.decisions.impl.*;
import aprove.api.decisions.results.*;
import aprove.api.impl.*;
import aprove.input.Programs.cint.Translator;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;

public enum CintProblemDecisionsFactory {
    ;

    private static final boolean BACKEND_EXISTS = LocalToolDetector.cintBackendExists("koat")
                                                  || LocalToolDetector.cintBackendExists("loat");

    public static Optional<ProblemDecisions>
           create(ProblemInputImpl problemInput) throws ProblemDecisionsInstantiationException {
        if (BACKEND_EXISTS) {
            return ProblemDecisionsImpl.create(new AnalyzableProblemInputCreator(problemInput,
                                                                         CintProblemDecisionsFactory::belongsToProtoAnnotation,
                                                                         CintProblemDecisionsFactory::toProtoAnnotation),
                                               Optional.empty(),
                                               Optional.empty(),
                                               Optional.of(SymbolDecisionImpl.createWithoutModing(loadSymbols(problemInput.getPath()))),
                                               Optional.empty());
        } else {
            throw new ProblemDecisionsInstantiationException("KoAT or LoAT is required to analyze cint-files!");
        }
    }

    private static Set<FunctionSymbol> loadSymbols(Path problemPath) throws ProblemDecisionsInstantiationException {
        try {
            Translator cintTranslator = new Translator();
            // This is a hack. Set some symbol as proto-annotation (and thus as the symbol to be analyzed)
            // to force STARTTERM FUNCTIONSYMBOLS s.t. the translation succeeds.
            cintTranslator.setProtoAnnotation("symbol");
            cintTranslator.translate(problemPath.toFile());
            if (cintTranslator.getState() == null) {
                throw new TranslationException("Translator returned null!");
            }
            assert cintTranslator.getState() instanceof CpxIntTrsProblem;
            return ((CpxIntTrsProblem) cintTranslator.getState()).getDefinedSymbols();
        } catch (FileNotFoundException | TranslationException e) {
            e.printStackTrace();
            throw new ProblemDecisionsInstantiationException("Parsing failed!", e);
        }
    }

    private static boolean belongsToProtoAnnotation(String line) {
        return line.startsWith("(STARTTERM");
    }

    private static String toProtoAnnotation(ProblemDecisionResults problemDecisionResults) {
        return problemDecisionResults.getSymbol();
    }
}
