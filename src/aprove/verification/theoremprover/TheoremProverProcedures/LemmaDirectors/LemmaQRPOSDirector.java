package aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * LemmaDirector using a QRPOS
 *
 * @author dickmeis
 *
 */

public class LemmaQRPOSDirector extends LemmaDirector {

    public LemmaQRPOSDirector(Program program, int minimalHeuristic) {
        super(program, minimalHeuristic);
    }

    public LemmaQRPOSDirector(Program program) {
        this(program, 1);
    }

    @Override
    AbortableConstraintSolver<TRSTerm> newSolver(Set<FunctionSymbol> programSignature,
            HashSet solverConfiguration) {

        // without this distinction the solver would cause an
        // ArrayOutOfBounds-Exception
        if (solverConfiguration != null && !solverConfiguration.isEmpty()){

            // ugly workaround for javac
            //(a generic type casted to a non-generic type makes trouble...)
            ExtHashSetOfQuasiStatuses<FunctionSymbol> cast = (ExtHashSetOfQuasiStatuses<FunctionSymbol>) solverConfiguration;

            return QRPOSBreadthSolver.create(programSignature, cast);
        }
        else{
            return QRPOSBreadthSolver.create(programSignature);
        }
    }

    @Override
    protected HashSet getSolverConfiguration(AbortableConstraintSolver abstractConstraintSolver) {
        return ((QRPOSBreadthSolver)abstractConstraintSolver).getAllFinalStatuses();
    }

    @Override
    public HashSet createNewSolverConfiguration() {
        return ExtHashSetOfQuasiStatuses.create();
    }

}
