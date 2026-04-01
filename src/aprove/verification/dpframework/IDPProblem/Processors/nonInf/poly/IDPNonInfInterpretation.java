/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import immutables.*;


public class IDPNonInfInterpretation extends IDPGInterpretation {

    public static IDPNonInfInterpretation
    create(
        final boolean isNat,
        final boolean isTupleNat,
        final IDPRuleAnalysis ruleAnalysis,
        final IdpShapeHeuristic maxHeuristic,
        final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory,
        final GPolyFactory<BigIntImmutable, GPolyVar> innerFactory,
        final ConstraintFactory<BigIntImmutable> constraintFactory,
        final FlatteningVisitor<BigIntImmutable, GPolyVar> inner,
        final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outer,
        final CoeffOrder<BigIntImmutable> coeffOrderParam,
        final List<Citation> citationsParam,
        final OPCRange<BigIntImmutable> coeffRange,
        final BigIntImmutable maxCoeffValueParam,
        Abortion aborter) throws AbortionException {
        return new IDPNonInfInterpretation(isNat, isTupleNat, ruleAnalysis, maxHeuristic, factory, innerFactory, constraintFactory,
            inner, outer, coeffOrderParam, citationsParam, coeffRange, maxCoeffValueParam, aborter);
    }


    protected final NonInfBound nonInfBound;
    protected final OrderPoly<BigIntImmutable> nonInfBoundPoly;
    protected final Map<TRSTerm, ImmutablePair<NonInfArbitraryConstant, OrderPoly<BigIntImmutable>>> nonInfArbitraryConstants;


    protected IDPNonInfInterpretation(
            final boolean isNat,
            final boolean isTupleNat,
            final IDPRuleAnalysis ruleAnalysis,
            final IdpShapeHeuristic maxHeuristic,
            GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factoryParam,
            GPolyFactory<BigIntImmutable, GPolyVar> innerFactoryParam,
            ConstraintFactory<BigIntImmutable> constraintFactoryParam,
            FlatteningVisitor<BigIntImmutable, GPolyVar> inner,
            FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outer,
            CoeffOrder<BigIntImmutable> coeffOrderParam,
            List<Citation> citationsParam,
            OPCRange<BigIntImmutable> coeffRange,
            BigIntImmutable maxCoeffValueParam, Abortion aborter)
                throws AbortionException {
        super(isNat, isTupleNat, ruleAnalysis, maxHeuristic, factoryParam, innerFactoryParam, constraintFactoryParam, inner, outer,
                coeffOrderParam, citationsParam, coeffRange,
                maxCoeffValueParam, aborter);
        this.nonInfBound = new NonInfBound();
        this.nonInfBoundPoly = this.factory.buildFromCoeff(this.factory.getInnerFactory().buildFromVariable(this.nonInfBound));
        this.nonInfArbitraryConstants = new LinkedHashMap<TRSTerm, ImmutablePair<NonInfArbitraryConstant, OrderPoly<BigIntImmutable>>>();
    }

    @Override
    public IDPNonInfInterpretation specialize(
            final Map<GPolyVar, BigIntImmutable> state,
            final Map<OPCLogVar<BigIntImmutable>, Boolean> logState,
            final BigIntImmutable defValue, Abortion aborter)
                throws AbortionException {
        synchronized(this) {
            this.extendedAfs = null;
            IDPNonInfInterpretation specialization =
                new IDPNonInfInterpretation(this.isNat, this.isTupleNat, this.ruleAnalysis, this.maxHeuristic, this.factory.getFactory(), this.factory.getInnerFactory(),
                        this.constraintFactory,
                        this.fvInner, this.fvOuter, this.coeffOrder,
                        this.citations,
                        this.coeffRange, this.maxPredefCoeffValue, aborter);
            this.applySpecialization(specialization, state, logState, defValue, aborter);
            return specialization;
        }
    }

    @Override
    protected void applySpecialization(
            final GInterpretation<BigIntImmutable> spec,
            final Map<GPolyVar, BigIntImmutable> state,
            final Map<OPCLogVar<BigIntImmutable>, Boolean> logState,
            final BigIntImmutable defValue,
            Abortion aborter) throws AbortionException {
        IDPNonInfInterpretation specialization = (IDPNonInfInterpretation)spec;
        super.applySpecialization(spec, state, logState, defValue, aborter);
        specialization.nonInfArbitraryConstants.putAll(this.nonInfArbitraryConstants);
    }

    public NonInfBound getNonInfBound() {
        return this.nonInfBound;
    }

    public OrderPoly<BigIntImmutable> getNonInfBoundPoly() {
        return this.nonInfBoundPoly;
    }

    public NonInfArbitraryConstant getConstant(TRSTerm term) {
        return this.getArbitraryConstantPair(term).x;
    }

    @Override
    public OrderPoly<BigIntImmutable> interpretAsArbitraryConstant(TRSTerm term) {
        return this.getArbitraryConstantPair(term).y;
    }

    protected ImmutablePair<NonInfArbitraryConstant, OrderPoly<BigIntImmutable>> getArbitraryConstantPair(TRSTerm term) {
        ImmutablePair<NonInfArbitraryConstant, OrderPoly<BigIntImmutable>> res = this.nonInfArbitraryConstants.get(term);
        if (res == null) {
            NonInfArbitraryConstant c = new NonInfArbitraryConstant(term);
            res = new ImmutablePair<NonInfArbitraryConstant, OrderPoly<BigIntImmutable>>(c, this.factory.buildFromInnerVariable(c));
            this.nonInfArbitraryConstants.put(term, res);
        }
        return res;
    }

}
