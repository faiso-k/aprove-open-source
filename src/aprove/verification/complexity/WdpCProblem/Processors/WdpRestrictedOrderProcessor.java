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
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.GInterpretationModeStronglyLinear.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Implements Corollary 18 from
 * "Automated Complexity Analysis Based on the Dependency Pairs Method" by
 * Moser, Hirokawa
 */
public class WdpRestrictedOrderProcessor extends WdpProblemProcessor {

    private final boolean allowArgumentFiltering;
    private final int degree;
    private final int range;
    private final OPCSolver<BigIntImmutable> opcSolver;

    @ParamsViaArgumentObject
    public WdpRestrictedOrderProcessor(Arguments arguments) {
        this.allowArgumentFiltering = arguments.allowArgumentFiltering;
        this.degree = arguments.degree;
        this.range = arguments.range;
        this.opcSolver = arguments.opcSolver;
    }

    @Override
    protected boolean isWdpApplicable(WDPProblemRC obl) {
        return true;
    }

    @Override
    protected Result processWdp(WDPProblemRC wdpProblem, Abortion aborter) throws AbortionException {
        Set<FunctionSymbol> definedSymbols = new LinkedHashSet<FunctionSymbol>();
        definedSymbols.addAll(wdpProblem.getDefinedRSymbols());
        definedSymbols.addAll(wdpProblem.getDefinedPSymbols());

        Order<TRSTerm> order = this.findOrder(this.degree, wdpProblem, definedSymbols, aborter);
        if (order != null) {
            return ResultFactory.provedWithValue(
                    ComplexityYNM.createUpper(ComplexityValue.fixedDegreePoly(degree)),
                    new WdpRestrictedOrderProof(order, degree));
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
            /* Extend ignores already interpreted function symbols,
             * the sets do not need to be disjunct.
             */
            cs.gInterpretation.extend(
                    wdpProblem.getCompoundSymbols(),
                    new GInterpretationModeStronglyLinear<BigIntImmutable>(ConstantPart.VAR),
                    aborter);
            cs.gInterpretation.extend(
                    definedSymbols,
                    new GInterpretationModeLinear<BigIntImmutable>(),
                    aborter);
            Set<FunctionSymbol> allSymbols =
                aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(wdpProblem.getR());
            allSymbols.addAll(
                    aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(wdpProblem.getP()));
            cs.gInterpretation.extend(
                    allSymbols,
                    new GInterpretationModeLinear<BigIntImmutable>(cs.boolRange, null),
                    aborter);
        }

        /* Add constraints for rules & pairs */
        {
            Iterable<Rule> rp = IterableConcatenator.create(rules, wdpProblem.getP());
            Set<Constraint<TRSTerm>> ruleTC =
                Constraint.fromRules(rp, OrderRelation.GR);
            Set<OrderPolyConstraint<BigIntImmutable>> ruleOPCs =
                cs.gInterpretation.fromTermConstraints(ruleTC, aborter);
            constraintSet.add(cs.commentedAnd("Rules + Pairs", ruleOPCs));
        }

        /* Add monotonicity constraints */
        if (this.allowArgumentFiltering && wdpProblem.isInnermost()) {
            constraintSet.add(
                    cs.constraintFactory.createComment(
                            "monotonicity constraints",
                            this.monotoneConstraintsWithFiltering(wdpProblem, cs, rules)));
        }else {
            Set<OrderPolyConstraint<BigIntImmutable>> monotonicityOPCs =
                cs.gInterpretation.getStrongMonotonicityConstraints();
            constraintSet.add(
                    cs.commentedAnd("monotonicity constraints", monotonicityOPCs));
        }

        OrderPolyConstraint<BigIntImmutable> finalConstraint =
            cs.constraintFactory.createAnd(constraintSet);
        finalConstraint = cs.constraintFactory.createQuantifierE(
                finalConstraint, finalConstraint.getFreeVariables());

        return cs.solveConstraint(finalConstraint, aborter);
    }

    private OrderPolyConstraint<BigIntImmutable> monotoneConstraintsWithFiltering(
            WDPProblemRC wdpProblem,
            final ConstraintStuff cs,
            final ImmutableSet<Rule> rules) {
        Set<OrderPolyConstraint<BigIntImmutable>> constraintSet =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        Iterable<Rule> itRules = IterableConcatenator.create(rules, wdpProblem.getP());
        Map<FunctionSymbol, BitSet> monotonicityRequirements =
            new LinkedHashMap<FunctionSymbol, BitSet>();
        for (Rule r : itRules) {
            this.computeMonotonicityRequirements(
                    r.getRight(),
                    wdpProblem.getDefinedRSymbols(),
                    monotonicityRequirements);
        }

        for (Map.Entry<FunctionSymbol,BitSet> e : monotonicityRequirements.entrySet()) {
            FunctionSymbol fs = e.getKey();
            BitSet monReq = e.getValue();

            Set<OrderPolyConstraint<BigIntImmutable>> constraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();;
            List<OrderPoly<BigIntImmutable>> monVars =
                BigIntImmutableRing.getStrongMonotonicityConstraints(
                    cs.gInterpretation, fs, constraints, cs.boolRange);
            constraintSet.addAll(constraints);

            int arity = fs.getArity();
            for (int i = 0; i < arity; i++) {
                if (monReq.get(i)) {
                    OrderPolyConstraint<BigIntImmutable> constraint =
                        cs.gtConstraint(monVars.get(i), cs.orderPolyFactory.getZero());
                    constraintSet.add(constraint);
                }
            }
        }
        return cs.commentedAnd("Monotonicity Requirements", constraintSet);
    }

    /**
     * Computes the monotonicity requirements of function symbols in term
     * t and stores them in monotonicityRequirements.
     *
     * A position has to be monotone if there is a defined function symbol
     * below this position
     */
    private boolean computeMonotonicityRequirements(TRSTerm t,
            ImmutableSet<FunctionSymbol> definedRSymbols,
            Map<FunctionSymbol,BitSet> monotonicityRequirements) {
        if (t.isVariable()) {
            return false;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol rootsym = fa.getRootSymbol();

        int arity = rootsym.getArity();
        BitSet usablePositions = new BitSet(arity);
        for (int i = 0; i < arity; i++ ) {
            TRSTerm subterm = fa.getArgument(i);
            if (this.computeMonotonicityRequirements(subterm, definedRSymbols, monotonicityRequirements)) {
                usablePositions.set(i);
            }
        }

        boolean hasDefinedInSubterm = !usablePositions.isEmpty();
        if (hasDefinedInSubterm) {
            BitSet monReq = monotonicityRequirements.get(rootsym);
            if (monReq == null) {
                monotonicityRequirements.put(rootsym, usablePositions);
            } else {
                monReq.or(usablePositions);
            }
        }

        return hasDefinedInSubterm || definedRSymbols.contains(rootsym);
    }

    static class WdpRestrictedOrderProof extends Proof.DefaultProof {

        private final Order<TRSTerm> order;
        private final int degree;

        public WdpRestrictedOrderProof(Order<TRSTerm> order, int degree) {
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
        public boolean allowArgumentFiltering;
        public int degree;
        public int range;
        public OPCSolver<BigIntImmutable> opcSolver;
    }
}
