package aprove.solver;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;

/**
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PMatroArcticSMTFactory extends SolverFactory {

    /**
     * Some ID for serialization.
     */
    private static final long serialVersionUID = 1L;

    /**
     * The dimension of the matrices to use.
     */
    private final int dimension;

    /**
     * Whether to use below zero or not.
     */
    private final boolean belowZero;

    @ParamsViaArgumentObject
    public PMatroArcticSMTFactory(Arguments arguments) {
        super(arguments);
        this.belowZero = arguments.belowZero;
        this.dimension = arguments.dimension;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        return PMatroArcticSMTSolver.create(
                new YicesEngine(), this.dimension, this.belowZero);
    }

    public static class Arguments extends SolverFactory.Arguments {
        public boolean belowZero;
        public int dimension;
    }

    @Override
    public boolean deliversCPForders() {
        return true;
    }

}
