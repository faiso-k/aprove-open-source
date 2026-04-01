package aprove.verification.idpframework.Polynomials.Interpretation;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.ShapeHeuristics.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class PolyIntInterpretation extends PolyInterpretation<BigInt> {

    /**
     * @return an empty interpretation. the polynomials of predefined functions
     * in simple or simple mixed mode.
     */
    public static PolyIntInterpretation create(
        final PolyShapeHeuristic<BigInt> defaultMode,
        final ItpfFactory constraintFactory,
        final FreshVarGenerator freshVarGenerator) {
        return new PolyIntInterpretation(defaultMode,
            constraintFactory, freshVarGenerator, Collections.<Citation> emptyList());
    }

    protected PolyIntInterpretation(
            final PolyShapeHeuristic<BigInt> defaultMode,
            final ItpfFactory constraintFactory,
            final FreshVarGenerator freshVarGenerator,
            final List<Citation> citationsParam) {
        super(BigInt.ZERO, defaultMode, constraintFactory,
            freshVarGenerator, citationsParam);
    }

    @Override
    public PolyIntInterpretation specialize(final Map<IVariable<BigInt>, BigInt> state,
        final Map<ItpfLogVar, Boolean> logState) {
        synchronized (this) {
            this.extendedAfs = null;
            final PolyIntInterpretation specialization =
                new PolyIntInterpretation(this.shapeHeuristic,
                    this.constraintFactory, this.freshVarGenerator, this.citations);
            this.applySpecialization(specialization, state, logState);
            return specialization;
        }
    }

    @Override
    protected <R extends SemiRing<R>> RelDependency getPredefinedV_f_i(final IFunctionSymbol<R> fs,
        final int argNr) {
        if (fs.isPredefinedFunction()) {
            if (fs.getResultDomain().getRing().isBoundedRing()) {
                return RelDependency.Wild;
            } else {
                final PredefinedFunction<?, ?> func =
                    (PredefinedFunction<?, ?>) fs.getSemantics();
                switch (func.getFunc()) {
                case Add:
                case Sub:
                case Mul:
                    break;
                case Div:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Wild;
                    case 1:
                        return RelDependency.Wild;
                    }
                    break;
                case Mod:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Wild;
                    case 1:
                        return RelDependency.Wild;
                    }
                    break;
                case Eq:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Wild;
                    case 1:
                        return RelDependency.Wild;
                    }
                    break;
                case Ge:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Independent;
                    case 1:
                        return RelDependency.Independent;
                    }
                    break;
                case Gt:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Independent;
                    case 1:
                        return RelDependency.Independent;
                    }
                    break;
                case Lt:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Independent;
                    case 1:
                        return RelDependency.Independent;
                    }
                    break;
                case Le:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Independent;
                    case 1:
                        return RelDependency.Independent;
                    }
                    break;
                case UnaryMinus:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Decreasing;
                    }
                    break;
                default:
                    throw new UnsupportedOperationException("unknown function " + fs.getSemantics());
                }
            }
        }
        return null;
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getContextPolyFromFunction(final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final IFunctionSymbol<I> fs) {

        Polynomial<BigInt> result;
        if (PredefinedUtil.isFunction(fs, Func.Div)) {
            result =
                this.getPolyDiv(fs, relDependency, activeCondition);
        } else if (PredefinedUtil.isFunction(fs, Func.Mod)) {
            result =
                this.getPolyMod(fs, relDependency, activeCondition);
        } else {
            throw new IllegalArgumentException("can not interpret function "
                + fs);
        }
        return result;
    }

    private Polynomial<BigInt> getPolyDiv(final IFunctionSymbol<?> symbol,
        final RelDependency relDependency,
        final IActiveCondition activeCondition) {
        Polynomial<BigInt> result;

        final ImmutablePair<Polynomial<BigInt>, Polynomial<BigInt>> contextSwitchCoeff =
            this.getContextPolySwitchCoeff(relDependency, activeCondition, true);

        if (contextSwitchCoeff.x.isOne() && contextSwitchCoeff.y.isOne()) {
            return this.factory.zero(this.ring);
        }

        final PolyVariable<BigInt> x1 =
            this.getVariableForFunctionSymbolArgument(symbol, 0);
        final Polynomial<BigInt> x1Poly = this.factory.create(x1);
        final Polynomial<BigInt> x1NegPoly = x1Poly.negate();
        final Polynomial<BigInt> absX1 = this.factory.max(this.ring, x1Poly, x1NegPoly);

        // get offset
        Polynomial<BigInt> offsetPoly = null;
        final PolyVariable<BigInt> x2 =
            this.getVariableForFunctionSymbolArgument(symbol, 1);
        final Polynomial<BigInt> x2Poly = this.factory.create(x2);
        final Polynomial<BigInt> x2NegPoly = x2Poly.negate();
        final Polynomial<BigInt> absX2 = this.factory.max(this.ring, x2Poly, x2NegPoly);
        // offsetPoly = min(absX2 - 1, absX1)
        offsetPoly = this.factory.min(this.ring, absX2.subtract(this.factory.one(this.ring)), absX1);

        final Polynomial<BigInt> coeffPoly = contextSwitchCoeff.x.subtract(contextSwitchCoeff.y);

        // (inc-dec) * (max(x1, -x1) - offsetPoly)
        // (inc - dec) decides for over and under approximation

        result = absX1.subtract(offsetPoly);
        result = coeffPoly.mult(result);

        return result;
    }

    private Polynomial<BigInt> getPolyMod(final IFunctionSymbol<?> symbol,
        final RelDependency relDependency,
        final IActiveCondition activeCondition) {
        Polynomial<BigInt> result;

        final ImmutablePair<Polynomial<BigInt>, Polynomial<BigInt>> contextSwitchCoeff =
            this.getContextPolySwitchCoeff(relDependency, activeCondition, true);

        if (contextSwitchCoeff.x.isOne() && contextSwitchCoeff.y.isOne()) {
            return this.factory.zero(this.ring);
        }

        // (inc - dec) * max(x2, -x2)
        // a decides for over and under approximation
        final PolyVariable<BigInt> x2 =
            this.getVariableForFunctionSymbolArgument(symbol, 1);
        final Polynomial<BigInt> x2Poly = this.factory.create(x2);
        final Polynomial<BigInt> x2NegPoly = x2Poly.negate();

        result =
        // (2a - 1) * max(x2, -x2)
            contextSwitchCoeff.x.subtract(contextSwitchCoeff.y).mult(
                this.factory.max(this.ring, x2Poly, x2NegPoly));

        return result;
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyAdd(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        final PolyVariable<BigInt> x1 =
            this.getVariableForFunctionSymbolArgument(symbol, 0);
        final Monomial<BigInt> x1Monom =
            this.factory.createMonomial(this.ring, ImmutableCreator.create(Collections.singletonMap(
                x1, BigInt.ONE)));
        final PolyVariable<BigInt> x2 =
            this.getVariableForFunctionSymbolArgument(symbol, 1);
        final Monomial<BigInt> x2Monom =
            this.factory.createMonomial(this.ring, ImmutableCreator.create(Collections.singletonMap(
                x2, BigInt.ONE)));
        final Map<Monomial<BigInt>, BigInt> polyMap =
            new LinkedHashMap<Monomial<BigInt>, BigInt>();
        polyMap.put(x1Monom, BigInt.ONE);
        polyMap.put(x2Monom, BigInt.ONE);
        return this.factory.create(this.ring, ImmutableCreator.create(polyMap));
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyEq(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.zero(this.ring);
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyFalse(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.zero(this.ring);
//        return factory.create(getNextCoeff(symbol));
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyGe(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.zero(this.ring);
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyGt(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.zero(this.ring);
    }

    @Override
    protected Polynomial<BigInt> getPolyInt(final IFunctionSymbol<BigInt> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.create(PredefinedUtil.getIntValue(symbol,
            symbol.getResultDomain()));
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyLand(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.zero(this.ring);
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyLe(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.zero(this.ring);
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyLnot(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.zero(this.ring);
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyLor(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.zero(this.ring);
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyLt(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.zero(this.ring);
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyMul(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        final PolyVariable<BigInt> x1 =
            this.getVariableForFunctionSymbolArgument(symbol, 0);
        final PolyVariable<BigInt> x2 =
            this.getVariableForFunctionSymbolArgument(symbol, 1);
        final Map<PolyVariable<BigInt>, BigInt> polyMap =
            new LinkedHashMap<PolyVariable<BigInt>, BigInt>();
        polyMap.put(x1, BigInt.ONE);
        polyMap.put(x2, BigInt.ONE);
        return this.factory.create(
            this.factory.createMonomial(this.ring, ImmutableCreator.create(polyMap)),
            BigInt.ONE);
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolySub(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        final PolyVariable<BigInt> x1 =
            this.getVariableForFunctionSymbolArgument(symbol, 0);
        final Monomial<BigInt> x1Monom =
            this.factory.createMonomial(this.ring, ImmutableCreator.create(Collections.singletonMap(
                x1, BigInt.ONE)));
        final PolyVariable<BigInt> x2 =
            this.getVariableForFunctionSymbolArgument(symbol, 1);
        final Monomial<BigInt> x2Monom =
            this.factory.createMonomial(this.ring, ImmutableCreator.create(Collections.singletonMap(
                x2, BigInt.ONE)));
        final Map<Monomial<BigInt>, BigInt> polyMap =
            new LinkedHashMap<Monomial<BigInt>, BigInt>();
        polyMap.put(x1Monom, BigInt.ONE);
        polyMap.put(x2Monom, BigInt.ONE.negate());
        return this.factory.create(this.ring, ImmutableCreator.create(polyMap));
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyTrue(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        return this.factory.zero(this.ring);
    }

    @Override
    protected <I extends SemiRing<I>> Polynomial<BigInt> getPolyUnaryMinus(final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<BigInt> form) {
        final PolyVariable<BigInt> x1 =
            this.getVariableForFunctionSymbolArgument(symbol, 0);
        return this.factory.create(
            this.factory.createMonomial(this.ring, ImmutableCreator.create(Collections.singletonMap(
                x1, BigInt.ONE))), BigInt.ONE.negate());
    }

}
