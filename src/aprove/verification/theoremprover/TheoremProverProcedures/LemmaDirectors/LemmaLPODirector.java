package aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * LemmaDirector using an LPO
 *
 * @author dickmeis
 *
 */

public class LemmaLPODirector extends LemmaDirector {

    public LemmaLPODirector(Program program, int minimalHeuristic) {
        super(program, minimalHeuristic);
    }

    public LemmaLPODirector(Program program) {
        this(program, 1);
    }

    @Override
    AbortableConstraintSolver<TRSTerm> newSolver(Set<FunctionSymbol> programSignature,
            HashSet solverConfiguration) {

        // without this distinction the solver would cause an
        // ArrayOutOfBounds-Exception
        if (solverConfiguration != null && !solverConfiguration.isEmpty()){
            return LPOBreadthSolver.create(programSignature, (ExtHashSetOfPosets<FunctionSymbol>) solverConfiguration );
        } else {
            return LPOBreadthSolver.create(programSignature);
        }
    }

    @Override
    protected HashSet getSolverConfiguration(AbortableConstraintSolver<TRSTerm> abstractConstraintSolver){
        return ((LPOBreadthSolver)abstractConstraintSolver).getAllFinalPrecedences();
    }

    @Override
    public HashSet createNewSolverConfiguration(){
        ExtHashSetOfPosets<String> conf = ExtHashSetOfPosets.create();
        return conf;
    }
}
