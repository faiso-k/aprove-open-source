/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.util.*;

import aprove.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * This implementation of OPCSolver transforms the OPC to SimplePolyConstraints
 * and uses some (already existing) solver to handle these constraints.
 * @author cotto
 */
public class RATtoFormula implements OPCSolver<PoT> {
    /**
     * The polynomial ring.
     */
    private Ring<GPoly<PoT, GPolyVar>> polyRing;

    /**
     * The flattening visitor for coefficient polynomials.
     */
    private FlatteningVisitor<PoT, GPolyVar> fvInner;

    /**
     * The flattening visitor for order polynomials.
     */
    private FlatteningVisitor<GPoly<PoT, GPolyVar>, GPolyVar> fvOuter;

    /**
     * This sat engine will try to solve the resulting formula.
     */
    private final SatEngine backend;

    @ParamsViaArguments("satBackend")
    public RATtoFormula(SatEngine satBackend) {
        this.backend = satBackend;
    }

    /**
     * Solve the given constraint (encapsulating the single constraints).
     * @param constraint Some OrderPolyConstraint that should be solved.
     * @param ranges The range for the variables.
     * @param defaultRange The range for the variables not mentioned in ranges.
     * @return A value for every variable.
     * @param aborter Some aborter.
     * @throws AbortionException when the aborter kicks in.
     */
    @Override
    public Map<GPolyVar, PoT> solve(
            final OrderPolyConstraint<PoT> constraint,
            final Map<GPolyVar, OPCRange<PoT>> ranges,
            final OPCRange<PoT> defaultRange,
            final Abortion aborter) throws AbortionException {
        int min = defaultRange.getList().get(0).x.getPair().y.intValue();
        int max = defaultRange.getList().get(0).y.getPair().y.intValue();
        Ring<PoT> innerRing = (Ring<PoT>)this.fvInner.getRingC();
        VariableConverterPoT varConv =
            new VariableConverterPoT(innerRing);
        if (Globals.useAssertions) {
            assert (defaultRange.getList() != null
                    && defaultRange.getList().size() == 1);
        }

        aborter.checkAbortion();
        RATExtractFormulaVisitor cv = new RATExtractFormulaVisitor(
                innerRing, this.polyRing, this.fvInner.getMonoid(),
                this.fvInner, this.fvOuter, ranges, min, max, varConv);
        cv.applyToWithCleanup(constraint);
        Formula<None> formula = cv.getFormula();
        aborter.checkAbortion();
        int[] solution;
        try {
            solution = this.backend.getSATChecker().solve(formula, aborter);
        } catch (SolverException e) {
            solution = null;
        }
        Map<GPolyVar, PoT> map = null;
        if (solution != null) {
            varConv.setSolution(solution);
            varConv.setTransformed(cv.getTransformed());
            map = varConv.getMap();
        }
        varConv.clear();
        return map;
    }

    /**
     * @param polyRingParam the polynomial ring.
     */
    @Override
    public void setPolyRing(
            final Ring<GPoly<PoT, GPolyVar>> polyRingParam) {
        this.polyRing = polyRingParam;
    }

    /**
     * @param inner the flattening visitor for coefficient polynomials.
     */
    @Override
    public void setFvInner(
            final FlatteningVisitor<PoT, GPolyVar> inner) {
        this.fvInner = inner;
    }

    /**
     * @param outer the flattening visitor for order polynomials.
     */
    @Override
    public void setFvOuter(
            final FlatteningVisitor<GPoly<PoT, GPolyVar>, GPolyVar>
                outer) {
        this.fvOuter = outer;
    }

    @Override
    public OPCSolver<PoT> getCopy() {
        RATtoFormula copy = new RATtoFormula(this.backend);
        copy.polyRing = this.polyRing;
        return copy;
    }

    @Override
    public Map<GPolyVar, PoT> solve(OrderPolyConstraint<PoT> constraint,
            Domain domain, Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException();
    }
}
