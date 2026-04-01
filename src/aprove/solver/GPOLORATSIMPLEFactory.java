package aprove.solver;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.RatHeuristic.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;


/**
 * A GPOLORATSIMPLEFactory takes the parameters and creates the
 * GPOLORATSIMPLESolver when asked to do so.
 * @author Carsten Otto
 * @version $Id$
 */
public class GPOLORATSIMPLEFactory extends SolverFactory {

    // some constants for specifying certain degrees
    public static final int SIMPLE_MIXED = Interpretation.SIMPLE_MIXED;
    public static final int SIMPLE = Interpretation.SIMPLE;
    public static final int LINEAR = Interpretation.LINEAR;

    /**
     * Some ID for serialization.
     */
    private static final long serialVersionUID = 1L;

    /**
     * The heuristic to use to know where non-natural coefficients may be used.
     */
    private final Heuristic heur;

    /**
     * The form of the to-be-constructed polynomials.
     */
    private final GInterpretationMode<MbyN> form;

    /**
     * The range of the numerator (0 up to this value).
     */
    private final int rangeNumerator;

    /**
     * The degree of the denominator (1 up to this value).
     */
    private final int rangeDenominator;

    /**
     * The domain, if used in The GPoloRatSimple
     */
    private final Domain domain;

    /**
     * The solver will be used to transform the general OrderPolyConstraints
     * to some simple format that can actually be solved. The resulting form of
     * the constraints depends on the solver being used. Any OPCSolver starts
     * the embedded solver after simplifying the constraints and returns the
     * solver's result.
     */
    private final OPCSolver<MbyN> opcSolver;

    /**
     * The strict mode that should be used.
     */
    private final StrictMode strictMode;

    @ParamsViaArgumentObject
    public GPOLORATSIMPLEFactory(Arguments arguments) {
        super(arguments);
        this.form = GInterpretationMode.createFromLegacy(
                arguments.degree,
                arguments.maxSimpleDegree < 0 ? Integer.MAX_VALUE : arguments.maxSimpleDegree);
        this.rangeDenominator = arguments.denominatorRange;
        this.rangeNumerator = arguments.numeratorRange;
        this.domain = arguments.domain;
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
        return new QDPGPoloRatSimpleSolver(this.form, this.rangeNumerator,
                this.rangeDenominator, this.domain, this.strictMode,
                this.opcSolver.getCopy(), ratHeur);
    }

    public static class Arguments extends SolverFactory.Arguments {
        public int degree;
        public int denominatorRange;
        public Domain domain;
        public Heuristic heuristic;
        /**
         * The maximum degree used in simple and simple mixed interpretations
         * (useful for function symbols with high arity).
         */
        public int maxSimpleDegree;
        public int numeratorRange;
        public OPCSolver<MbyN> opcSolver;
        public StrictMode strictMode;
    }

    @Override
    public boolean deliversCPForders() {
        return true;
    }
}
