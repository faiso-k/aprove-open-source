package aprove.solver;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.dpframework.TRSProblem.Solvers.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.ArcticInt.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PMatroArcticFactory extends SolverFactory {
    private static final Logger log = Logger.getLogger("aprove.solver.PMatroArcticFactory");

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
     * Whether to use binary or unary encoding for SAT.
     */
    private final boolean unary;

    /**
     * If applicable (wrt technique and obligation):
     * use collapsing interpretations for tuple symbols, i.e.,
     * interpret "DP terms" as numbers instead of vectors?
     */
    private final boolean collapse;

    /**
     * If we are using below-zero interpretations:
     * - True: Use "absolute positiveness" as descriped by
     *   Koprowski and Waldmann in their RTA'08 paper,
     *   i.e., the constant "addend" must be positive.
     * - False: Require "somewhere positiveness" as described by
     *   Sternagel and Thiemann in their RTA'14 paper,
     *   i.e., the constant addend or some coefficient matrix
     *   must be positive.
     */
    private final boolean absPos;

    @ParamsViaArgumentObject
    public PMatroArcticFactory(Arguments arguments) {
        super(arguments);
        this.dimension = arguments.dimension;
        this.max = arguments.max;
        this.min = arguments.min;
        this.unary = arguments.unary;
        this.collapse = arguments.collapse;
        this.absPos = arguments.absPos;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        FormulaFactory<None> formulaFactory =
            new aprove.verification.oldframework.PropositionalLogic.Formulae.FullSharingFactory<None>();
        CircuitFactory circuitFactory;
        ExoticIntBinarizer<ArcticInt> binarizer;
        if (this.unary) {
            circuitFactory = new ArcticIntUnaryCircuitFactory(formulaFactory);
            binarizer = new ExoticIntUnarizer<ArcticInt>(
                    ArcticIntFactory.create(), circuitFactory);

            // hack for side conditions from plus/times circuits,
            // not only from encoded atomic arctic expressions
            ((ArcticIntUnaryCircuitFactory)circuitFactory).setUnarizer((ExoticIntUnarizer<ArcticInt>)binarizer);
        } else {
            circuitFactory = new ArcticIntCircuitFactory(formulaFactory);
            binarizer = new ExoticIntBinarizer<ArcticInt>(
                    ArcticIntFactory.create(), circuitFactory);
        }

        final int min, max;
        if (this.min > 0) {
            PMatroArcticFactory.log.warning("Illegal strategy parameter for PMatroArcticInt: 'Min = " + this.min + "'! Defaulting to 0.");
            min = 0;
        } else {
            min = this.min;
        }
        if (this.max < 0) {
            PMatroArcticFactory.log.warning("Illegal strategy parameter for PMatroArcticInt: 'Max = " + this.max + "'! Defaulting to 0.");
            max = 0;
        } else {
            max = this.max;
        }
        String description = "with arctic " + (min < 0 ? "integers" : "natural numbers");
        List<Citation> citations = new ArrayList<Citation>();
        citations.add(Citation.ARCTIC);
        if (min < 0 && !this.absPos) {
            citations.add(Citation.STERNAGEL_THIEMANN_RTA14);
        }
        return new PMatroExoticSolver<ArcticInt>(this.getEngine(), this.dimension,
                ArcticInt.create(min), ArcticInt.create(max),
                ArcticSemiring.create(), ArcticIntOrder.create(),
                ArcticIntFactory.create(), binarizer,
                circuitFactory, this.collapse, description, citations,
                this.absPos);
    }

    @Override
    public RRRSolver getRRRSolver() {
        return new RRRMatroArcticSolver(this);
    }

    /**
     * @return whether the setting of this factory make it a
     *  factory for "below zero" arctic orders.
     */
    public boolean isBelowZero() {
        return this.min < 0;
    }

    public static class Arguments extends SolverFactory.Arguments {
        public int dimension;
        public int max;
        public int min;
        public boolean unary;
        public boolean collapse;
        public boolean absPos;
    }
    
    @Override
    public boolean deliversCPForders() {
        return true;
    }

}
