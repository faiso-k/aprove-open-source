/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.Nat.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.FullSharingFactory;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class NatOPCSatSolver implements LogOPCSolver<BigIntImmutable> {

    final SatEngine engine;

    @ParamsViaArgumentObject
    public NatOPCSatSolver(Arguments arguments) {
        this.engine = arguments.engine;
    }

    @Override
    public void setFvInner(FlatteningVisitor<BigIntImmutable, GPolyVar> inner) {
        // TODO Auto-generated method stub

    }

    @Override
    public void setFvOuter(
            FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outer) {
        // TODO Auto-generated method stub

    }

    @Override
    public void setPolyRing(Ring<GPoly<BigIntImmutable, GPolyVar>> polyRingParam) {
        // TODO Auto-generated method stub

    }

    @Override
    public Pair<Map<GPolyVar, BigIntImmutable>, Map<OPCLogVar<BigIntImmutable>, Boolean>> solveLog (
            OrderPolyConstraint<BigIntImmutable> constraint,
            Map<GPolyVar, OPCRange<BigIntImmutable>> ranges,
            OPCRange<BigIntImmutable> defaultRange, Abortion aborter)
            throws AbortionException {
        if (aprove.Globals.useAssertions) {
            for (OPCRange<BigIntImmutable> range : ranges.values()) {
                assert(range.getList().get(0).x.getBigInt().signum() == 0);
            }
            assert(defaultRange.getList().get(0).x.getBigInt().signum() == 0);
        }
        Map<GPolyVar, BigIntImmutable> simpleRanges = new LinkedHashMap<GPolyVar, BigIntImmutable>();
        for (Map.Entry<GPolyVar, OPCRange<BigIntImmutable>> range : ranges.entrySet()) {
            simpleRanges.put(range.getKey(), range.getValue().getList().get(0).y);
        }
        FullSharingFactory<None> formulaFactory = new FullSharingFactory<None>();
        CircuitFactory circuitFactory = new NatCircuitFactory(formulaFactory);
        Binarizer<BigIntImmutable> binarizer = new NatBinarizer(circuitFactory);
        PolyToCircuitConverter<BigIntImmutable, GPolyVar> circConv = new PolyToCircuitConverter<BigIntImmutable, GPolyVar> (circuitFactory, binarizer, simpleRanges, defaultRange.getList().get(0).y);
        OPCtoFormulaConverter<BigIntImmutable> converter = new OPCtoFormulaConverter<BigIntImmutable>(circConv, formulaFactory);
        // System.err.println("RANGES: " + defaultRange + " " + ranges);
        aborter.checkAbortion();
        converter.applyToWithCleanup(constraint);

        Formula<None> solveMe = formulaFactory.buildAnd(binarizer.getRangeConstraint(), converter.getFormulaWithCleanup());
        aborter.checkAbortion();
        int[] solution;
        try {
            solution = this.engine.getSATChecker().solve(solveMe, aborter);
        } catch (SolverException e) {
            return null;
        }
        if (solution != null) {
            binarizer.setInterpretation(solution);
            return new Pair<Map<GPolyVar, BigIntImmutable>, Map<OPCLogVar<BigIntImmutable>, Boolean>>(binarizer.getSubstitution(), converter.getLogState(solution));
        } else {
            return null;
        }
     }

    public SatEngine getEngine() {
        return this.engine;
    }


    @Override
    public Map<GPolyVar, BigIntImmutable> solve(
            OrderPolyConstraint<BigIntImmutable> constraint,
            Map<GPolyVar, OPCRange<BigIntImmutable>> ranges,
            OPCRange<BigIntImmutable> defaultRange, Abortion aborter)
            throws AbortionException {
        Pair<Map<GPolyVar, BigIntImmutable>, Map<OPCLogVar<BigIntImmutable>, Boolean>> solution = this.solveLog(constraint, ranges, defaultRange, aborter);
        if (solution != null) {
            return solution.x;
        } else {
            return null;
        }
    }

    public static class Arguments {
        public SatEngine engine;
    }

    @Override
    public OPCSolver<BigIntImmutable> getCopy() {
        Arguments args = new Arguments();
        args.engine = this.engine;
        NatOPCSatSolver copy = new NatOPCSatSolver(args);
        return copy;
    }

    @Override
    public Map<GPolyVar, BigIntImmutable> solve(
            OrderPolyConstraint<BigIntImmutable> constraint, Domain domain,
            Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException();
    }

}
