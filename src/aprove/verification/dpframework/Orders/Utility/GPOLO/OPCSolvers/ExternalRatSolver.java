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
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * WARNING: Only for testing. The result might be wrong if one of the following
 * conditions is met:
 * x) The default range only allows 0 as valid result
 * x) Some non-boolean variable has a range that is not the default range
 * x) The exponent does not range from -a to a.
 * @author cotto
 */
@NoParams
public class ExternalRatSolver implements OPCSolver<PoT> {
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

    @Override
    public Map<GPolyVar, PoT> solve(
            final OrderPolyConstraint<PoT> constraint,
            final Map<GPolyVar, OPCRange<PoT>> ranges,
            final OPCRange<PoT> defaultRange,
            final Abortion aborter) throws AbortionException {
        BigInteger min = defaultRange.getList().get(0).x.getPair().y;
        BigInteger max = defaultRange.getList().get(0).y.getPair().y;
        if (Globals.useAssertions) {
            assert (defaultRange.getList() != null
                    && defaultRange.getList().size() == 1);
            assert (min.negate().equals(max));
        }

        Ring<PoT> innerRing = (Ring<PoT>)this.fvInner.getRingC();
        RATExternalExtractFormulaVisitor cv = new RATExternalExtractFormulaVisitor(
                innerRing, this.polyRing, this.fvInner.getMonoid(),
                this.fvInner, this.fvOuter, ranges, min, max);
        cv.applyToWithCleanup(constraint);
        Formula<Diophantine> formula = cv.getFormula();
        BigInteger rangeMax = min.abs().max(max.abs());
        DefaultValueMap<String, BigInteger> newRanges =
            new DefaultValueMap<String, BigInteger>(BigInteger.valueOf(2l).pow(rangeMax.intValue()));
        SearchAlgorithm ratSolver = RatSolverFileSearch.create(newRanges);
        FormulaToSPCsVisitor formulaToSPCs = new FormulaToSPCsVisitor();
        formula.apply(formulaToSPCs);
        Pair<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>> spcs =
            formulaToSPCs.getPair();
        Map<String, BigInteger> solution = null;
        if (spcs != null) {
            solution = ratSolver.search(spcs.x, spcs.y, aborter);
        }
        Map<GPolyVar, PoT> map = null;
        if (solution != null) {
            map = new LinkedHashMap<GPolyVar, PoT>(solution.size());
            for (Map.Entry<String, BigInteger> entry : solution.entrySet()) {
                GPolyVar var = GAtomicVar.createVariable(entry.getKey());
                BigInteger value = entry.getValue();
                PoT newValue;
                if (value.signum() >= 0) {
                    newValue = PoT.create(value);
                } else {
                    // -4 = -1 * 2^2
                    newValue = PoT.create(value);
                    if (Globals.useAssertions) {
                        // newValue = -1*2^j
                        assert (newValue.getPair().x.equals(
                                BigInteger.valueOf(-1)));
                    }
                    // 1*2^(-2) = 1/4
                    newValue = PoT.create(BigInteger.ONE,
                            newValue.getPair().y.negate());
                }
                map.put(var, newValue);
            }
        }
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
        ExternalRatSolver copy = new ExternalRatSolver();
        copy.polyRing = this.polyRing;
        return copy;
    }

    @Override
    public Map<GPolyVar, PoT> solve(OrderPolyConstraint<PoT> constraint,
            Domain domain, Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException();
    }

}
