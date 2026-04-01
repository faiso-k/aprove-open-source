/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This implementation of OPCSolver transforms the OPC to SimplePolyConstraints
 * and uses some (already existing) solver to handle these constraints.
 * The constraints must be built using MbyN coefficients.
 * @author cotto
 */
public class MbyNtoFormula implements OPCSolver<MbyN> {
    /**
     * The polynomial ring.
     */
    private Ring<GPoly<MbyN, GPolyVar>> polyRing;

    /**
     * The flattening visitor for coefficient polynomials.
     */
    private FlatteningVisitor<MbyN, GPolyVar> fvInner;

    /**
     * The flattening visitor for order polynomials.
     */
    private FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar>
        fvOuter;

    /**
     * The solver that can handle SPCs.
     */
    private final SPCSolver solver;

    /**
     * If this variable is set all denominators will be set to the maximal
     * value that the denominators' range allows.
     */
    private final boolean denomFixed;

    /**
     * If a domain is used instead of the ranges map this one is not null via
     * default in Arguments
     */
    private Domain domain;

    public static long encodeTime;
    public static long solveTime;
    public static long decodeTime;

    @ParamsViaArgumentObject
    public MbyNtoFormula(Arguments arguments) {
        this.denomFixed = arguments.fixDenominator;
        this.solver = arguments.solver;
        this.converter = null;
    }

    /**
     * For directly searching on rational constraints we us ratSearch and
     * therefore have a converter, the engine and the string format at this
     * place
     */
    private final MbyNSMTConverter converter;

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
    public Map<GPolyVar, MbyN> solve(
            final OrderPolyConstraint<MbyN> constraint,
            final Map<GPolyVar, OPCRange<MbyN>> ranges,
            final OPCRange<MbyN> defaultRange,
            final Abortion aborter) throws AbortionException {

        BigInteger denominator = null;
        if (this.denomFixed)  {
            denominator =
                defaultRange.getList().get(0).y.getNumerator();
        }
        VariableConverterMbyN varConv = null;
        if (this.domain != null) {
            varConv = new VariableConverterMbyN(Domain
                    .getLCMofDenominator(this.domain));
        } else {
            varConv = new VariableConverterMbyN(denominator);
        }
        assert (varConv != null);
        Ring<MbyN> innerRing = (Ring<MbyN>)this.fvInner.getRingC();
        aborter.checkAbortion();
        MbyNExtractFormulaVisitor cv = new MbyNExtractFormulaVisitor(
                innerRing, this.polyRing, this.fvInner.getMonoid(),
                this.fvInner, this.fvOuter, ranges, varConv, defaultRange,
                denominator);
        cv.applyToWithCleanup(constraint);

        final Formula<Diophantine> formula = cv.getFormula();
        final Map<String, BigInteger> rangesFormula = cv.getRanges();
        if (Globals.useAssertions) {
            assert (defaultRange.getList() != null
                    && defaultRange.getList().size() == 1);
        }
        // the default range contains a single MbyN value where the numerator
        // gives the range for the numerators, the denominator gives the range
        // for the denominators.
        BigInteger defaultRangeNum =
            defaultRange.getList().get(0).x.getNumerator();
        BigInteger defaultRangeDenom =
            defaultRange.getList().get(0).y.getNumerator();
        BigInteger defaultRangeInt =
            defaultRangeNum.max(defaultRangeDenom);
        aborter.checkAbortion();
        FormulaToSPCsVisitor formulaToSPCs = new FormulaToSPCsVisitor();
        formula.apply(formulaToSPCs);
        Pair<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>> spcs =
            formulaToSPCs.getPair();
        Map<GPolyVar, BigInteger> solution = null;
        aborter.checkAbortion();
        if (spcs != null) {
            solution = this.solver.search(spcs.x, spcs.y, rangesFormula,
                    defaultRangeInt, aborter);
        }
        Map<GPolyVar, MbyN> map = null;
        if (solution != null) {
            varConv.setSolution(solution);
            varConv.setNumeratorsAndDenominators(
                    cv.getNumerators(), cv.getDenominators());
            map = varConv.getMap();
        }
        return map;
    }

    @Override
    public Map<GPolyVar, MbyN> solve(OrderPolyConstraint<MbyN> constraint,
            Domain domain, Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException();
    }
    /**
     * @param polyRingParam the polynomial ring.
     */
    @Override
    public void setPolyRing(
            final Ring<GPoly<MbyN, GPolyVar>> polyRingParam) {
        this.polyRing = polyRingParam;
    }

    /**
     * @param inner the flattening visitor for coefficient polynomials.
     */
    @Override
    public void setFvInner(
            final FlatteningVisitor<MbyN, GPolyVar> inner) {
        this.fvInner = inner;
    }

    /**
     * @param outer the flattening visitor for order polynomials.
     */
    @Override
    public void setFvOuter(
            final FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar>
                outer) {
        this.fvOuter = outer;
    }

    /**
     * @return whether the denominator is fixed or not
     */
    public boolean getDenomFixed() {
        return this.denomFixed;
    }

    @Override
    public OPCSolver<MbyN> getCopy() {
        Arguments arguments = new Arguments();
        arguments.solver = this.solver;
        arguments.fixDenominator = this.denomFixed;
        MbyNtoFormula copy = new MbyNtoFormula(arguments);
        copy.polyRing = this.polyRing;
        return copy;
    }

    public static class Arguments {
        public SPCSolver solver;

        /**
         *  Fix the denominator to the maximal value of its range
         */
        public boolean fixDenominator;
    }

}
