package aprove.solver;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * A factory for PMatroNatSolvers.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PMatroNatFactory extends SolverFactory {

    /**
     * Some ID for serialization.
     */
    private static final long serialVersionUID = 1L;

    private final int dimension;

    private final int range;

    /**
     * max value a sum may take; <= 0 means unbounded
     */
    private final int maxSumValue;

    /**
     * max value a product may take; <= 0 means unbounded
     */
    private final int maxProductValue;

    /**
     * If applicable (wrt technique and obligation):
     * use collapsing interpretations for tuple symbols, i.e.,
     * interpret "DP terms" as numbers instead of vectors?
     */
    private final boolean collapse;

    @ParamsViaArgumentObject
    public PMatroNatFactory(Arguments arguments) {
        super(arguments);
        this.dimension       = arguments.dimension;
        this.range           = arguments.range;
        this.maxSumValue     = arguments.maxSumValue;
        this.maxProductValue = arguments.maxProductValue;
        this.collapse        = arguments.collapse;
    }

    @Override
    public PMatroNatSolver getQActiveSolver() {
        String description = "to (N^" +
            this.dimension + ", +, *, >=, >)";
        List<Citation> citations = new ArrayList<Citation>();
        return new PMatroNatSolver(this.getEngine(), this.dimension,
                BigIntImmutable.create(BigInteger.valueOf(this.range)),
                BigIntImmutable.create(BigInteger.valueOf(this.maxSumValue)),
                BigIntImmutable.create(BigInteger.valueOf(this.maxProductValue)),
                this.collapse, description, citations);
    }

    @Override
    public RRRSolver getRRRSolver() {
        return this.getQActiveSolver();
    }

    @Override
    public RRRMuSolver getRRRMuSolver() {
        return this.getQActiveSolver();
    }

    @Override
    public SCNPOrderEncoder getSCNPOrderEncoder(FormulaFactory<None> formulaFactory) {
        return this.getQActiveSolver();
    }


    public static class Arguments extends SolverFactory.Arguments {
        public int dimension;
        public int range;
        public int maxSumValue;
        public int maxProductValue;
        public boolean collapse;
    }
    
    @Override
    public boolean deliversCPForders() {
        return true;
    }

}
