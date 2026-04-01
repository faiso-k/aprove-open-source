package aprove.api.decisions.factory;

import java.util.*;

import aprove.api.decisions.*;
import aprove.api.impl.*;

public class ProblemDecisionsFactory {

    public static Optional<ProblemDecisions>
           createProblemDecisions(ProblemInputImpl problemInput) throws ProblemDecisionsInstantiationException {
        switch (problemInput.getFileExtension()) {
            case "trs":
                return TRSProblemDecisionsFactory.create(problemInput);
            case "cint":
                return CintProblemDecisionsFactory.create(problemInput);
            case "hs":
                return HaskellProblemDecisionsFactory.create(problemInput);
            case "pl":
                return PrologProblemDecisionsFactory.create(problemInput);
            case "llvm":
                return LLVMProblemDecisionsFactory.create(problemInput);
            case "c":
                return CProblemDecisionsFactory.create(problemInput);
            default:
                return UnknownProblemDecisionsFactory.create(problemInput);
        }
    }
}
