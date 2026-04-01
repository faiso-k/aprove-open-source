package aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * LemmaDirector using an RPO
 *
 * @author dickmeis
 *
 */

public class LemmaRPODirector extends LemmaDirector {

    public LemmaRPODirector(Program program, int minimalHeuristic) {
        super(program, minimalHeuristic);
    }

    public LemmaRPODirector(Program program) {
        this(program, 1);
    }

    @Override
            AbortableConstraintSolver<TRSTerm> newSolver(Set<FunctionSymbol> programSignature,
                    HashSet solverConfiguration) {

        // without this distinction the solver would cause an
        // ArrayOutOfBounds-Exception
        if (solverConfiguration != null && !solverConfiguration.isEmpty()){
            return RPOBreadthSolver.create(programSignature,
                    (ExtHashSetOfPosets<FunctionSymbol>) solverConfiguration );
        } else {
            return RPOBreadthSolver.create(programSignature);
        }
    }

    @Override
    protected HashSet getSolverConfiguration(AbortableConstraintSolver abstractConstraintSolver){
        return ((RPOBreadthSolver)abstractConstraintSolver).getAllFinalPrecedences();
    }

    @Override
    public HashSet createNewSolverConfiguration(){
        ExtHashSetOfPosets<String> conf = ExtHashSetOfPosets.create();
        return conf;
    }
}