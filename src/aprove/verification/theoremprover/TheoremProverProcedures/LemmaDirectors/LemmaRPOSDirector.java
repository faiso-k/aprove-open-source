package aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * LemmaDirector using a RPOS
 *
 * @author dickmeis
 *
 */

public class LemmaRPOSDirector extends LemmaDirector {

    public LemmaRPOSDirector(Program program, int minimalHeuristic) {
        super(program, minimalHeuristic);
    }

    public LemmaRPOSDirector(Program program) {
        this(program, 1);
    }

    @Override
    AbortableConstraintSolver<TRSTerm> newSolver(Set<FunctionSymbol> programSignature,
            HashSet solverConfiguration) {

        // without this distinction the solver would cause an
        // ArrayOutOfBounds-Exception
        if (solverConfiguration != null && !solverConfiguration.isEmpty()) {
            return RPOSBreadthSolver.create(programSignature,
                    (ExtHashSetOfStatuses<FunctionSymbol>) solverConfiguration);
        } else {
            return RPOSBreadthSolver.create(programSignature);
        }
    }

    @Override
    protected HashSet getSolverConfiguration(AbortableConstraintSolver abstractConstraintSolver) {
        return ((RPOSBreadthSolver)abstractConstraintSolver).getAllFinalStatuses();
    }

    @Override
    public HashSet createNewSolverConfiguration() {
        return ExtHashSetOfStatuses.create();
    }

}
