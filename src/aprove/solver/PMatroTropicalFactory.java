package aprove.solver;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.ArcticInt.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * @author Ulrich Schmidt-Goertz
 */
public class PMatroTropicalFactory extends SolverFactory {

    /**
     * Some ID for serialization.
     */
    private static final long serialVersionUID = 1L;

    /**
     * The dimension of the matrices to use.
     */
    private final int dimension;

    /**
     * The minimum value to use for coefficients.
     */
    private final int min;

    /**
     * The maximum value to use for coefficients.
     */
    private final int max;

    /**
     * If applicable (wrt technique and obligation):
     * use collapsing interpretations for tuple symbols, i.e.,
     * interpret "DP terms" as numbers instead of vectors?
     */
    private final boolean collapse;

    @ParamsViaArgumentObject
    public PMatroTropicalFactory(Arguments arguments) {
        super(arguments);
        this.dimension = arguments.dimension;
        this.max = arguments.max;
        this.min = arguments.min;
        this.collapse = arguments.collapse;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        FormulaFactory<None> formulaFactory =
            new aprove.verification.oldframework.PropositionalLogic.Formulae.FullSharingFactory<None>();
        CircuitFactory circuitFactory = new TropicalIntCircuitFactory(formulaFactory);
        ExoticIntBinarizer<TropicalInt> binarizer =
            new ExoticIntBinarizer<TropicalInt>(TropicalIntFactory.create(), circuitFactory);
        String description = "with tropical " + (this.min < 0 ? "integers" : "natural numbers");
        List<Citation> citations = new ArrayList<Citation>();
        // citations.add(Citation.ARCTIC);  TODO
        return new PMatroExoticSolver<TropicalInt>(this.getEngine(), this.dimension,
                TropicalInt.create(this.min), TropicalInt.create(this.max),
                TropicalSemiring.create(), TropicalIntOrder.create(),
                TropicalIntFactory.create(), binarizer,
                circuitFactory, this.collapse, description, citations, false);
    }

    public static class Arguments extends SolverFactory.Arguments {
        public int dimension;
        public int max;
        public int min;
        public boolean collapse;
    }
    
    @Override
    public boolean deliversCPForders() {
        return false;
    }

}
