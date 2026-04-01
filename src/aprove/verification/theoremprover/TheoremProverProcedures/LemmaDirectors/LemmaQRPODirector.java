package aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * LemmaDirector using an QRPO
 *
 * @author dickmeis
 *
 */

public class LemmaQRPODirector extends LemmaDirector {

    public LemmaQRPODirector(Program program, int minimalHeuristic) {
        super(program, minimalHeuristic);
    }

    public LemmaQRPODirector(Program program) {
        this(program, 1);
    }

    @Override
    AbortableConstraintSolver<TRSTerm> newSolver(Set<FunctionSymbol> programSignature,
            HashSet solverConfiguration) {

        // without this distinction the solver would cause an
        // ArrayOutOfBounds-Exception
        if (solverConfiguration != null && !solverConfiguration.isEmpty()){
            return QRPOBreadthSolver.create(programSignature,
                    (ExtHashSetOfQosets<FunctionSymbol>) solverConfiguration );
        } else {
            return QRPOBreadthSolver.create(programSignature);
        }
    }

    @Override
    protected HashSet getSolverConfiguration(AbortableConstraintSolver abstractConstraintSolver){
        return ((QRPOBreadthSolver)abstractConstraintSolver).getAllFinalPrecedences();
    }

    @Override
    public HashSet createNewSolverConfiguration(){
        ExtHashSetOfQosets<String> conf = ExtHashSetOfQosets.create();
        return conf;
    }
}