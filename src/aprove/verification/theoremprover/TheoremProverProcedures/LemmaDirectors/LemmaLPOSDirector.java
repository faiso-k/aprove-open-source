package aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * LemmaDirector using a LPOS
 *
 * @author dickmeis
 *
 */

public class LemmaLPOSDirector extends LemmaDirector {

    public LemmaLPOSDirector(Program program, int minimalHeuristic) {
        super(program, minimalHeuristic);
    }

    public LemmaLPOSDirector(Program program) {
        this(program, 1);
    }

    @Override
    AbortableConstraintSolver<TRSTerm> newSolver(Set<FunctionSymbol> programSignature,
            HashSet solverConfiguration) {

        // without this distinction the solver would cause an
        // ArrayOutOfBounds-Exception
        if (solverConfiguration != null && !solverConfiguration.isEmpty()) {
            return LPOSBreadthSolver.create(programSignature,
                    (ExtHashSetOfStatuses<FunctionSymbol>) solverConfiguration);
        } else {
            return LPOSBreadthSolver.create(programSignature);
        }
    }

    @Override
    protected HashSet getSolverConfiguration(AbortableConstraintSolver abstractConstraintSolver) {
        return ((LPOSBreadthSolver)abstractConstraintSolver).getAllFinalStatuses();
    }

    @Override
    public HashSet createNewSolverConfiguration() {
        return ExtHashSetOfStatuses.create();
    }

}
