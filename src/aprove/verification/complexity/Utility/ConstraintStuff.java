package aprove.verification.complexity.Utility;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Helper class containing everything needed to create polynom constraints
 * over BigIntImmutable (i.e. natural numbers)
 */
public class ConstraintStuff {
    /**
     * This visitor generates flat representations of OrderPolys, where the
     * coefficients will not be flattened (depending on the factory used to
     * create the flattening visitor).
     */
    public final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fvOuter;

    /**
     * This visitor generates flat representations of the inner polynomials,
     * which are coefficients of the outer polynomials.
     */
    public final FlatteningVisitor<BigIntImmutable, GPolyVar> fvInner;

    /**
     * The default range for the variables.
     */
    public final OPCRange<BigIntImmutable> range;

    /**
     * This factory will be used to create new order polynomials.
     */
    public final OrderPolyFactory<BigIntImmutable> orderPolyFactory;

    /**
     * This factory can create the outer polynomials. It will be used in the
     * orderPolyFactory and interpretation.
     */
    public final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>
        outerPolyFactory;

    /**
     * This factory will be used to create new polynomials
     * (coefficients of order polynomials).
     */
    public final GPolyFactory<BigIntImmutable, GPolyVar> coeffPolyFactory;

    /**
     * This solver is able to take OPCs and provide some solution.
     */
    public final OPCSolver<BigIntImmutable> solver;

    /**
     * This factory will be used to create order poly constraints
     */
    public final ConstraintFactory<BigIntImmutable> constraintFactory =
        new SimpleFactory<BigIntImmutable>();

    public final GInterpretation<BigIntImmutable> gInterpretation;

    /**
     * Range for booleans
     *
     * Needed e.g. for GInterpretation.getActiveConditions().
     */
    public final OPCRange<BigIntImmutable> boolRange =
        new OPCRange<BigIntImmutable>(BigIntImmutable.ONE, BigIntImmutable.ONE);

    /**
     * Solution computed by the SAT solver. Available after solveConstraint
     * returned successfully.
     */
    public Map<GPolyVar, BigIntImmutable> solution;

    /**
     * Create the solver based on the given parameters.
     * @param rangeParam The range of the variables.
     * @param monotoneParam Find a monotone ordering?
     * @param opcSolver The solver that is able to transform and solve order
     * poly constraints.
     */
    public ConstraintStuff(
            final int rangeParam,
            final OPCSolver<BigIntImmutable> opcSolver,
            final List<Citation> citations) {
        BigIntImmutable rangeBigInt =
            BigIntImmutable.create(BigInteger.valueOf(rangeParam));
        this.range = new OPCRange<BigIntImmutable>(rangeBigInt, rangeBigInt);
        Ring<BigIntImmutable> ringC = new BigIntImmutableRing();
        CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<GPolyVar>();
        this.coeffPolyFactory = new FullSharingFactory<BigIntImmutable, GPolyVar>();
        this.outerPolyFactory = new FullSharingFactory<
                GPoly<BigIntImmutable, GPolyVar>, GPolyVar>();
        this.orderPolyFactory = new OrderPolyFactory<BigIntImmutable>(
                    this.outerPolyFactory, this.coeffPolyFactory);

        GPolyFlatRing<BigIntImmutable, GPolyVar> flatRing =
            new SimpleGPolyFlatRing<BigIntImmutable, GPolyVar>(ringC, monoid);
        this.fvInner = new FlatteningVisitor<BigIntImmutable, GPolyVar>(flatRing);

        GPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> flatRing2 =
            new SimpleGPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>,
                GPolyVar>(this.coeffPolyFactory, monoid);
        this.fvOuter =
            new FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(
                    flatRing2);

        opcSolver.setFvInner(this.fvInner);
        opcSolver.setFvOuter(this.fvOuter);
        opcSolver.setPolyRing(this.coeffPolyFactory);
        this.solver = opcSolver;

        CoeffOrder<BigIntImmutable> biiOrder = new BigIntImmutableOrder();
        this.gInterpretation = GInterpretation.create(this.outerPolyFactory, this.coeffPolyFactory,
                this.constraintFactory, this.fvInner, this.fvOuter, biiOrder, citations);

    }

    /**
     * Solves a constraint
     *
     * @param constraint constraint to be solved
     */
    public GPOLO<BigIntImmutable> solveConstraint(
            OrderPolyConstraint<BigIntImmutable> constraint, Abortion aborter)
            throws AbortionException {

        if (Globals.DEBUG_NOSCHINSKI) {
            OPCExportVisitor<BigIntImmutable> export =
                new OPCExportVisitor<BigIntImmutable>(this.fvInner, this.fvOuter, new PLAIN_Util());
            export.applyTo(constraint);
            System.err.println(export);
            System.err.println(this.gInterpretation);
        }

        this.solution = this.solver.solve(constraint, this.gInterpretation.getRanges(),
                    this.range, aborter);

        if (this.solution == null) {
            return null;
        }

        Ring<BigIntImmutable> ring = (Ring<BigIntImmutable>)this.fvInner.getRingC();

        // step 3, build some order out of the solution
        GInterpretation<BigIntImmutable> sgi =
            this.gInterpretation.specialize(this.solution, ring.zero(), aborter);
        GPOLONAT solvingOrder =
            new GPOLONAT(sgi, this.orderPolyFactory, this.fvInner, this.fvOuter);
        return solvingOrder;
    }

    public OrderPolyConstraint<BigIntImmutable> eqConstraint(
            OrderPoly<BigIntImmutable> one,
            OrderPoly<BigIntImmutable> two) {
        OrderPoly<BigIntImmutable> poly =
            this.orderPolyFactory.minus(one, two);
        return this.constraintFactory.createWithQuantifier(poly, ConstraintType.EQ);
    }

    public OrderPolyConstraint<BigIntImmutable> geConstraint(
            OrderPoly<BigIntImmutable> one,
            OrderPoly<BigIntImmutable> two) {
        OrderPoly<BigIntImmutable> poly =
            this.orderPolyFactory.minus(one, two);
        return this.constraintFactory.createWithQuantifier(poly, ConstraintType.GE);
    }

    public OrderPolyConstraint<BigIntImmutable> gtConstraint(
            OrderPoly<BigIntImmutable> one,
            OrderPoly<BigIntImmutable> two) {
        OrderPoly<BigIntImmutable> poly =
            this.orderPolyFactory.minus(one, two);
        return this.constraintFactory.createWithQuantifier(poly, ConstraintType.GT);
    }

    /**
     * @param cond OrderPoly with possible values 0 or 1
     */
    public OrderPolyConstraint<BigIntImmutable> condEqConstraint(
            OrderPoly<BigIntImmutable> cond,
            OrderPoly<BigIntImmutable> one,
            OrderPoly<BigIntImmutable> two) {
        OrderPoly<BigIntImmutable> poly =
            this.orderPolyFactory.minus(one, two);
        poly = this.orderPolyFactory.times(cond, poly);
        return this.constraintFactory.createWithQuantifier(poly, ConstraintType.EQ);
    }

    /**
     * @param cond OrderPoly with possible values 0 or 1
     */
    public OrderPolyConstraint<BigIntImmutable> condGeConstraint(
            OrderPoly<BigIntImmutable> cond,
            OrderPoly<BigIntImmutable> one,
            OrderPoly<BigIntImmutable> two) {
        OrderPoly<BigIntImmutable> poly =
            this.orderPolyFactory.minus(one, two);
        poly = this.orderPolyFactory.times(cond, poly);
        return this.constraintFactory.createWithQuantifier(poly, ConstraintType.GE);
    }

    /**
     * @param cond OrderPoly with possible values 0 or 1
     */
    public OrderPolyConstraint<BigIntImmutable> condGtConstraint(
            OrderPoly<BigIntImmutable> cond,
            OrderPoly<BigIntImmutable> one,
            OrderPoly<BigIntImmutable> two) {
        OrderPoly<BigIntImmutable> poly =
            this.orderPolyFactory.minus(one, two);
        poly = this.orderPolyFactory.times(cond, poly);
        poly = this.orderPolyFactory.plus(
                this.orderPolyFactory.minus(this.orderPolyFactory.getOne(), cond),
                poly);
        return this.constraintFactory.createWithQuantifier(poly, ConstraintType.GT);
    }

    public OrderPolyConstraint<BigIntImmutable> commentedAnd(
            String comment, Set<OrderPolyConstraint<BigIntImmutable>> constraints) {
        return this.constraintFactory.createComment(
                comment,
                this.constraintFactory.createAnd(constraints));
    }

    public OrderPoly<BigIntImmutable> makeOrderPolyFromVar(GPolyVar var) {
        GPoly<BigIntImmutable, GPolyVar> varPoly =
            this.coeffPolyFactory.buildFromVariable(var);
        return this.orderPolyFactory.buildFromCoeff(varPoly);
    }

}