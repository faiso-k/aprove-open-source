package aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * LemmaDirector using an QLPO
 *
 * @author dickmeis
 *
 */

public class LemmaQLPODirector extends LemmaDirector {

    public LemmaQLPODirector(Program program, int minimalHeuristic) {
        super(program, minimalHeuristic);
    }

    public LemmaQLPODirector(Program program) {
        this(program, 1);
    }

    @Override
    AbortableConstraintSolver<TRSTerm> newSolver(Set<FunctionSymbol> programSignature,
            HashSet solverConfiguration) {

        // without this distinction the solver would cause an
        // ArrayOutOfBounds-Exception
        if (solverConfiguration != null && !solverConfiguration.isEmpty()){
            return QLPOBreadthSolver.create(programSignature,
                    (ExtHashSetOfQosets<FunctionSymbol>) solverConfiguration );
        } else {
            return QLPOBreadthSolver.create(programSignature);
        }
    }

    @Override
    protected HashSet getSolverConfiguration(AbortableConstraintSolver abstractConstraintSolver){
        return ((QLPOBreadthSolver)abstractConstraintSolver).getAllFinalPrecedences();
    }

    @Override
    public HashSet createNewSolverConfiguration(){
        ExtHashSetOfQosets<String> conf = ExtHashSetOfQosets.create();
        return conf;
    }
}