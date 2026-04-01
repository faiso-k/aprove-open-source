package aprove.api.decisions.factory;

import java.util.*;

import aprove.api.decisions.*;
import aprove.api.decisions.impl.*;
import aprove.api.impl.*;

public enum UnknownProblemDecisionsFactory {
    ;

    public static Optional<ProblemDecisions>
           create(ProblemInputImpl problemInput) throws ProblemDecisionsInstantiationException {
        return ProblemDecisionsImpl.create(new AnalyzableProblemInputCreator(problemInput,
                                                                     line -> false,
                                                                     problemDecisionResults -> ""),
                                           Optional.empty(),
                                           Optional.empty(),
                                           Optional.empty(),
                                           Optional.empty());
    }
}
