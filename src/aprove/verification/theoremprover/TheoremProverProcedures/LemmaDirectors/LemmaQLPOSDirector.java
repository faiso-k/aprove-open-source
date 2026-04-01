package aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * LemmaDirector using an QLPOS
 *
 * @author dickmeis
 *
 */

public class LemmaQLPOSDirector extends LemmaDirector {

    public LemmaQLPOSDirector(Program program, int minimalHeuristic) {
        super(program, minimalHeuristic);
    }

    public LemmaQLPOSDirector(Program program) {
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

            return QLPOSBreadthSolver.create(programSignature, cast );
        }
        else {
            return QLPOSBreadthSolver.create(programSignature);
        }
    }

    @Override
    protected HashSet getSolverConfiguration(AbortableConstraintSolver abstractConstraintSolver){
        return ((QLPOSBreadthSolver)abstractConstraintSolver).getAllFinalStatuses();
    }

    @Override
    public HashSet createNewSolverConfiguration(){
        ExtHashSetOfQuasiStatuses conf = ExtHashSetOfQuasiStatuses.create();
        return conf;
    }
}