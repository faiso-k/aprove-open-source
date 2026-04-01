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
 * The constraints must be built using BigIntImmutable coefficients.
 * @author cotto
 */
public class NATtoFormula
    implements OPCSolver<BigIntImmutable> {
    /**
     * The polynomial ring.
     */
    private Ring<GPoly<BigIntImmutable, GPolyVar>> polyRing;

    /**
     * The flattening visitor for coefficient polynomials.
     */
    private FlatteningVisitor<BigIntImmutable, GPolyVar> fvInner;

    /**
     * The flattening visitor for order polynomials.
     */
    private FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>
        fvOuter;

    /**
     * The solver that can handle SPCs.
     */
    private final SPCSolver solver;

    @ParamsViaArguments("solver")
    public NATtoFormula(SPCSolver solver) {
        this.solver = solver;
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
    public Map<GPolyVar, BigIntImmutable> solve(
            final OrderPolyConstraint<BigIntImmutable> constraint,
            final Map<GPolyVar, OPCRange<BigIntImmutable>> ranges,
            final OPCRange<BigIntImmutable> defaultRange,
            final Abortion aborter) throws AbortionException {
        Ring<BigIntImmutable> innerRing = (Ring<BigIntImmutable>)this.fvInner.getRingC();
        NATExtractFormulaVisitor cv = new NATExtractFormulaVisitor(
                innerRing, this.polyRing, this.fvInner.getMonoid(),
                this.fvInner, this.fvOuter, ranges);
        aborter.checkAbortion();
        cv.applyToWithCleanup(constraint);
        aborter.checkAbortion();
        Formula<Diophantine> formula = cv.getFormula();
        Map<String, BigInteger> rangesFormula = cv.getRanges();
        if (Globals.useAssertions) {
            assert (defaultRange.getList() != null
                    && defaultRange.getList().size() == 1);
        }
        BigInteger defaultRangeInt =
            defaultRange.getList().get(0).y.getBigInt();
        FormulaToSPCsVisitor formulaToSPCs = new FormulaToSPCsVisitor();
        formula.apply(formulaToSPCs);
        aborter.checkAbortion();
        Pair<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>> spcs =
            formulaToSPCs.getPair();
        Map<GPolyVar, BigInteger> solution = null;
        if (spcs != null) {
            solution = this.solver.search(
                    spcs.x, spcs.y, rangesFormula, defaultRangeInt, aborter);
        }
        if (solution == null) {
            return null;
        }
        Map<GPolyVar, BigIntImmutable> solution2 =
            new LinkedHashMap<GPolyVar, BigIntImmutable>(solution.size());
        for (Map.Entry<GPolyVar, BigInteger> entry : solution.entrySet()) {
            BigIntImmutable bigIntImmutable =
                BigIntImmutable.create(entry.getValue());
            solution2.put(entry.getKey(), bigIntImmutable);
        }
        return solution2;
    }

    /**
     * @param polyRingParam the polynomial ring.
     */
    @Override
    public void setPolyRing(
            final Ring<GPoly<BigIntImmutable, GPolyVar>> polyRingParam) {
        this.polyRing = polyRingParam;
    }

    /**
     * @param inner the flattening visitor for coefficient polynomials.
     */
    @Override
    public void setFvInner(
            final FlatteningVisitor<BigIntImmutable, GPolyVar> inner) {
        this.fvInner = inner;
    }

    /**
     * @param outer the flattening visitor for order polynomials.
     */
    @Override
    public void setFvOuter(
            final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>
                outer) {
        this.fvOuter = outer;
    }

    @Override
    public OPCSolver<BigIntImmutable> getCopy() {
        NATtoFormula copy = new NATtoFormula(this.solver);
        copy.polyRing = this.polyRing;
        return copy;
    }

    @Override
    public Map<GPolyVar, BigIntImmutable> solve(
            OrderPolyConstraint<BigIntImmutable> constraint, Domain domain,
            Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException();
    }

}
