package aprove.solver;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.RatHeuristic.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * A GPOLORATFactory takes the parameters and creates the GPOLORATSolver when
 * asked to do so.
 * @author Carsten Otto
 */
public class GPOLORATFactory extends SolverFactory {

    // some constants for specifying certain degrees
    public static final int SIMPLE_MIXED = Interpretation.SIMPLE_MIXED;
    public static final int SIMPLE = Interpretation.SIMPLE;
    public static final int LINEAR = Interpretation.LINEAR;

    /**
     * Some ID for serializiation.
     */
    private static final long serialVersionUID = 1L;

    /**
     * The heuristic to use to know where non-natural coefficients may be used.
     */
    private final Heuristic heur;

    /**
     * The form of the to-be-constructed polynomials.
     */
    private final GInterpretationMode<PoT> form;

    /**
     * The smallest exponent that may be chosen for the variables.
     */
    private final int expMin;

    /**
     * The greatest exponent that may be chosen for the variables.
     */
    private final int expMax;

    /**
     * The solver will be used to transform the general OrderPolyConstraints
     * to some simple format that can actually be solved. The resulting form of
     * the constraints depends on the solver being used. Any OPCSolver starts
     * the embedded solver after simplifying the constraints and returns the
     * solver's result.
     */
    private final OPCSolver<PoT> opcSolver;

    /**
     * The strict mode that should be used.
     */
    private final StrictMode strictMode;

    @ParamsViaArgumentObject
    public GPOLORATFactory(Arguments arguments) {
        super(arguments);
        this.form = GInterpretationMode.createFromLegacy(
                arguments.degree,
                arguments.maxSimpleDegree < 0 ? Integer.MAX_VALUE : arguments.maxSimpleDegree);
        this.expMax = arguments.expMax;
        this.expMin = arguments.expMin;
        this.heur = arguments.heuristic;
        this.opcSolver = arguments.opcSolver;
        this.strictMode = arguments.strictMode;
    }

    /**
     * @return the solver that will work with the given parameters.
     */
    @Override
    public QActiveSolver getQActiveSolver() {
        RatHeuristic ratHeur =
            RatHeuristic.Heuristic.getRatHeuristic(this.heur);
        return new QDPGPoloRatSolver(this.form,
                this.expMin, this.expMax, this.strictMode, this.opcSolver.getCopy(),
                ratHeur);
    }

    public static class Arguments extends SolverFactory.Arguments {
        public int degree;
        public int expMax;
        public int expMin;
        public Heuristic heuristic;
        public int maxSimpleDegree;
        public OPCSolver<PoT> opcSolver;
        public StrictMode strictMode;
    }

    @Override
    public boolean deliversCPForders() {        
        return true;
    }
}
