package aprove.verification.complexity.WdpCProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.complexity.WdpCProblem.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.GInterpretationModeStronglyLinear.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Implements Corollary 35 from
 * "Automated Complexity Analysis Based on the Dependency Pairs Method" by
 * Moser, Hirokawa
 */
public class WdpReductionPairOrderProcessor extends WdpProblemProcessor {

    private final int degree;
    private final int range;
    private final OPCSolver<BigIntImmutable> opcSolver;

    @ParamsViaArgumentObject
    public WdpReductionPairOrderProcessor(Arguments arguments) {
        this.degree = arguments.degree;
        this.range = arguments.range;
        this.opcSolver = arguments.opcSolver;
    }

    @Override
    protected boolean isWdpApplicable(WDPProblemRC obl) {
        return !Rule.isDuplicating(obl.getR());
    }

    @Override
    protected Result processWdp(WDPProblemRC wdpProblem, Abortion aborter) throws AbortionException {
        Set<FunctionSymbol> definedSymbols =
            new LinkedHashSet<FunctionSymbol>();
        definedSymbols.addAll(wdpProblem.getDefinedRSymbols());
        definedSymbols.addAll(wdpProblem.getDefinedPSymbols());
        Order<TRSTerm> order = this.findOrder(this.degree, wdpProblem, definedSymbols, aborter);
        if (order != null) {
            return ResultFactory.provedWithValue(
                    ComplexityYNM.createUpper(ComplexityValue.fixedDegreePoly(degree)),
                    new WdpDirectComplexityProof(order, degree));
        }

        return ResultFactory.unsuccessful();
    }

    private Order<TRSTerm> findOrder(int degree, WDPProblemRC wdpProblem,
            Set<FunctionSymbol> definedSymbols, Abortion aborter) throws AbortionException {
        final List<Citation> citations = Collections.singletonList(Citation.POLO);
        final ConstraintStuff cs = new ConstraintStuff(this.range, this.opcSolver, citations);
        final ImmutableSet<Rule> rules = wdpProblem.getR();

        final Set<OrderPolyConstraint<BigIntImmutable>> constraintSet =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();

        /* Interpret function symbols */
        {
            GInterpretationMode<BigIntImmutable> form =
                new GInterpretationModeRestrictedWithAfs<BigIntImmutable>(
                        degree,definedSymbols, wdpProblem.getCompoundSymbols());
            cs.gInterpretation.extend(rules, form, aborter);
            cs.gInterpretation.extend(wdpProblem.getP(), form, aborter);
        }

        /* Add constraints for pairs */
        {
            Set<Constraint<TRSTerm>> pairTC =
                Constraint.fromRules(wdpProblem.getP(), OrderRelation.GR);
            Set<OrderPolyConstraint<BigIntImmutable>> pairOPCs =
                cs.gInterpretation.fromTermConstraints(pairTC, aborter);
            OrderPolyConstraint<BigIntImmutable> pairOPC =
                cs.constraintFactory.createAnd(pairOPCs);
            constraintSet.add(pairOPC);
        }

        /* Add usable rule constraints */
        {
            Map<Rule, QActiveCondition> usableRules =
                new LinkedHashMap<Rule, QActiveCondition>(rules.size());
            for (Rule r : rules) {
                usableRules.put(r, QActiveCondition.TRUE);
            }
            OrderPolyConstraint<BigIntImmutable> usableRuleOPC =
                cs.gInterpretation.getActiveRuleConstraints(usableRules,
                        null, cs.boolRange, aborter);
            constraintSet.add(usableRuleOPC);
        }

        /* Add usable rule SLI constraints */
        {
            Set<Rule> renamedRules = this.getRenamedRules(wdpProblem);
            cs.gInterpretation.extend(
                    aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(renamedRules),
                    new GInterpretationModeStronglyLinear<BigIntImmutable>(ConstantPart.ONE_PLUS_VAR),
                    aborter);
            Set<Constraint<TRSTerm>> sliTC =
                Constraint.fromRules(renamedRules, OrderRelation.GR);
            Set<OrderPolyConstraint<BigIntImmutable>> sliOPCs =
                cs.gInterpretation.fromTermConstraints(sliTC, aborter);
            OrderPolyConstraint<BigIntImmutable> sliOPC =
                cs.constraintFactory.createAnd(sliOPCs);
            constraintSet.add(sliOPC);
        }

        OrderPolyConstraint<BigIntImmutable> finalConstraint =
            cs.constraintFactory.createAnd(constraintSet);
        finalConstraint = cs.constraintFactory.createQuantifierE(
                finalConstraint, finalConstraint.getFreeVariables());

        return cs.solveConstraint(finalConstraint, aborter);
    }

    /**
     * Replaces FunctionSymbols in the set of rules by fresh ones.
     */
    private Set<Rule> getRenamedRules(WDPProblemRC wdpProblem) {
        Set<Rule> rules = wdpProblem.getR();
        Set<Rule> renamedRules = new LinkedHashSet<Rule>(rules);
        {
            Iterable<Rule> it = IterableConcatenator.create(rules, wdpProblem.getP());
            FreshNameGenerator fng = new FreshNameGenerator(
                    aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(it),
                    FreshNameGenerator.APPEND_NUMBERS);
            for (Rule r : rules) {
                TRSFunctionApplication lhs =
                    (TRSFunctionApplication)this.renameTerm(r.getLeft(), fng);
                TRSTerm rhs = this.renameTerm(r.getRight(), fng);
                renamedRules.add(Rule.create(lhs, rhs));
            }
        }
        return renamedRules;
    }

    /**
     * Replaces FunctionSymbols in a Term by fresh ones.
     */
    private TRSTerm renameTerm(TRSTerm t, FreshNameGenerator fng) {
        if (t instanceof TRSVariable) {
            return t;
        }

        TRSFunctionApplication fa = (TRSFunctionApplication)t;
        FunctionSymbol root = fa.getRootSymbol();
        FunctionSymbol newRoot = FunctionSymbol.create(
                fng.getFreshName(root.getName(), true), root.getArity());
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(root.getArity());
        for (TRSTerm oldArg : fa.getArguments()) {
            newArgs.add(this.renameTerm(oldArg, fng));
        }
        return TRSTerm.createFunctionApplication(newRoot, newArgs);
    }

    static class WdpDirectComplexityProof extends Proof.DefaultProof {

        private final Order<TRSTerm> order;
        private final int degree;

        public WdpDirectComplexityProof(Order<TRSTerm> order, int degree) {
            this.order = order;
            this.degree = degree;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            if (this.degree == 1) {
                sb.append(o.escape("Found linear restricted ordering:"));
            } else if (this.degree == 2) {
                sb.append(o.escape("Found quadratic restricted ordering:"));
            } else {
                sb.append(o.escape("Found restricted ordering of degree " + this.degree + ":"));
            }
            sb.append(o.newline());
            sb.append(o.export(this.order));
            return sb.toString();
        }

    }

    public static class Arguments {
        public int degree;
        public int range;
        public OPCSolver<BigIntImmutable> opcSolver;
    }

    private static class GInterpretationModeRestrictedWithAfs<C extends GPolyCoeff>
            extends GInterpretationMode<C> {

        private final Set<FunctionSymbol> definedSymbols;
        private Set<FunctionSymbol> compoundSymbols;

        private final GInterpretationMode<C> gimCompound;
        private final GInterpretationMode<C> gimConstants;
        private final GInterpretationMode<C> gimDefined;


        public GInterpretationModeRestrictedWithAfs(int degree, Set<FunctionSymbol> definedSymbols, Set<FunctionSymbol> compoundSymbols) {
            this.definedSymbols = definedSymbols;
            this.compoundSymbols = compoundSymbols;

            this.gimCompound = new GInterpretationModeStronglyLinear<C>(ConstantPart.VAR);
            this.gimConstants = new GInterpretationModeDegree<C>(1);
            this.gimDefined = new GInterpretationModeDegree<C>(degree);
        }

        @Override
        public OrderPoly<C> getPolynomial(final GInterpretation<C> interp,
            final FunctionSymbol fs,
            final List<OrderPoly<C>> variables) {
            if (this.definedSymbols.contains(fs)) {
                return this.gimDefined.getPolynomial(interp, fs, variables);
            } else if (this.compoundSymbols.contains(fs)){
                return this.gimCompound.getPolynomial(interp, fs, variables);
            } else {
                return this.gimConstants.getPolynomial(interp, fs, variables);
            }
        }

    }

}
