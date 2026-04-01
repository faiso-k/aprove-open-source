package aprove.solver;

import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics.*;

/**
 * Contains some common functionality for factories for
 * OpVarPolynomial-based negative POLOs.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class NegOpPOLOFactory extends SolverFactory {

    public static final String NEG_COEFF_HEURISTICS = "allowNegCoeffs";

    public static enum Heuristic {
        ALL_NEGATIVE, NON_CONST, PRHS, PRHS_NOT_TWICE, RLHS_NOT_NESTED_PRHS,
        RLHS_NOT_NESTED_PRHS_NOT_TWICE, DESTRUCTOR;
    }

    private final Heuristic heuristic;

    @ParamsViaArgumentObject
    public NegOpPOLOFactory(Arguments arguments) {
        super(arguments);
        this.heuristic = arguments.heuristic;
    }

    protected NCInterHeuristic getNCHeuristic() {
        switch (this.heuristic) {
        case ALL_NEGATIVE: return new FullNCInterHeuristic();
        case NON_CONST: return new NonConstNCInterHeuristic();
        case PRHS: return new PRhsNCInterHeuristic();
        case PRHS_NOT_TWICE: return new PRhsNotTwiceNCInterHeuristic();
        case RLHS_NOT_NESTED_PRHS: return new RLhsNotNestedNCInterHeuristic();
        case RLHS_NOT_NESTED_PRHS_NOT_TWICE: return new RLhsNotNestedPRhsNotTwiceNCInterHeuristic();
        case DESTRUCTOR: return new DestructorNCInterHeuristic();
        default: throw new RuntimeException("Heuristic " + this.heuristic +
                " not integrated yet.");
        }
    }

    public static class Arguments extends SolverFactory.Arguments {
        public Heuristic heuristic;
    }
}
