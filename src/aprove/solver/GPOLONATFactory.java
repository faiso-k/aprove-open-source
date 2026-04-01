package aprove.solver;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;


/**
 * A GPOLONATFactory takes the parameters and creates the GPOLONATSolver when
 * asked to do so.
 * @author Carsten Otto
 * @version $Id$
 */
public class GPOLONATFactory extends SolverFactory {
    /**
     * Some ID for serializiation.
     */
    private static final long serialVersionUID = 1L;

    /**
     * The form of the to-be-constructed polynomials.
     */
    private final GInterpretationMode<BigIntImmutable> form;

    /**
     * The range for the variables.
     */
    private final int range;

    /**
     * The solver will be used to transform the general OrderPolyConstraints
     * to some simple format that can actually be solved. The resulting form of
     * the constraints depends on the solver being used. Any OPCSolver starts
     * the embedded solver after simplifying the constraints and returns the
     * solver's result.
     */
    private final OPCSolver<BigIntImmutable> opcSolver;

    /**
     * The strict mode that should be used.
     */
    private final StrictMode strictMode;


    @ParamsViaArgumentObject
    public GPOLONATFactory(Arguments arguments) {
        super(arguments);
        this.form = GInterpretationMode.createFromLegacy(
                arguments.degree,
                arguments.maxSimpleDegree < 0 ? Integer.MAX_VALUE : arguments.maxSimpleDegree);
        this.opcSolver = arguments.opcSolver;
        this.range = arguments.range;
        this.strictMode = arguments.strictMode;
    }

    /**
     * @return the solver that will work with the given parameters.
     */
    @Override
    public QActiveSolver getQActiveSolver() {
        return new GPoloNatSolver(this.form, this.range,
                this.strictMode, this.opcSolver.getCopy());
    }

    /**
     * @return the solver that will work with the given parameters.
     */
    @Override
    public DirectSolver getDirectSolver() {
        return new GPoloNatSolver(this.form, this.range, null,
                this.opcSolver.getCopy());
    }

    /**
     * @return the solver that will work with the given parameters.
     */
    @Override
    public RRRSolver getRRRSolver() {
        return new GPoloNatSolver(this.form, this.range, null,
                this.opcSolver.getCopy());
    }

    public static class Arguments extends SolverFactory.Arguments {
        public int degree;
        public int maxSimpleDegree;
        public OPCSolver<BigIntImmutable> opcSolver;
        public int range;
        public StrictMode strictMode;
    }

    @Override
    public boolean deliversCPForders() {
        return true;
    }
}
