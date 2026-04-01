package aprove.verification.oldframework.Algebra.Orders.Solvers;

import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors.*;

public interface LemmaDirectorFactory {
    public LemmaDirector getLemmaDirector(Program program, int minimalHeuristic);
}
