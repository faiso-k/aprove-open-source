package aprove.api.decisions;

import java.util.*;
import java.util.function.*;

import aprove.api.*;

/**
 * This class is used to actually supply the missing information that is required by the {@link ProblemDecisions}.
 * For each possible decision, one supplied needs to be provided.
 * However, only the suppliers where a decision needs to be made will be called.
 */
public interface ProblemDecisionMaker {

    BeforeEvaluationStrategy decideHandlingMode(Supplier<String> decider);

    public static interface BeforeEvaluationStrategy {

        BeforeSymbol decideEvaluationStrategy(Supplier<String> decider);
    }

    public static interface BeforeSymbol {

        BeforeSymbolModing decideSymbol(Supplier<String> decider);
    }

    public static interface BeforeSymbolModing {

        BeforeQuery decideSymbolModing(Supplier<List<Boolean>> decider);
    }

    public static interface BeforeQuery {

        BeforeConstruct decideQuery(Supplier<String> decider);
    }

    public static interface BeforeConstruct {

        AnalyzableProblemInput construct() throws InvalidDecisionException;
    }
}
