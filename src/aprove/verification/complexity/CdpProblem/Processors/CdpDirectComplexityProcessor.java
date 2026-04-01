package aprove.verification.complexity.CdpProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdpProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.complexity.Utility.*;
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

/**
 * FIXME: Add documentation. There is not really a written down theory yet.
 */
public class CdpDirectComplexityProcessor extends CdpProblemProcessor {

    private final int degree;
    private final boolean incremental;
    private final int range;
    private final boolean useSimpleMixed;
    private final OPCSolver<BigIntImmutable> opcSolver;

    @ParamsViaArgumentObject
    public CdpDirectComplexityProcessor(final Arguments arguments) {
        this.degree = Math.abs(arguments.degree);
        this.incremental = arguments.incremental;
        this.range = arguments.range;
        this.useSimpleMixed = arguments.useSimpleMixed;
        this.opcSolver = arguments.opcSolver;
    }

    @Override
    protected boolean isCdpApplicable(final CdpProblem obl) {
        return true;
    }

    @Override
    protected Result processCdp(final CdpProblem cdpProblem, final Abortion aborter) throws AbortionException {
        final Set<Rule> usableRules = CdpUsableRulesProcessor.computeUsableRules(cdpProblem);

        for (final int computedDegree : this.computeDegreeList()) {
            final GPOLO<BigIntImmutable> order = this.findOrder(computedDegree, cdpProblem, usableRules, aborter);

            if (order != null) {
                if (Globals.useAssertions) {
                    final GInterpretation<BigIntImmutable> interpretation = order.getInterpretation();
                    SanityChecks.flatten(interpretation);

                    final LinkedHashSet<FunctionSymbol> definedSymbols =
                        new LinkedHashSet<>(cdpProblem.getDefinedRSymbols());
                    definedSymbols.addAll(cdpProblem.getDefinedPSymbols());
                    SanityChecks.constructorSymbolsStronglyLinear(interpretation, definedSymbols, true);
                }

                final Set<Rule> nonUsableRules = new LinkedHashSet<>(cdpProblem.getR());
                nonUsableRules.removeAll(usableRules);
                return ResultFactory.provedWithValue(
                    ComplexityYNM.createUpper(ComplexityValue.fixedDegreePoly(Math.abs(computedDegree))),
                    new CdpDirectComplexityProof(order, cdpProblem, nonUsableRules));
            }
        }

        return ResultFactory.unsuccessful();
    }

    private List<Integer> computeDegreeList() {
        if (!this.incremental) {
            return Collections.singletonList(this.useSimpleMixed ? -this.degree : this.degree);
        }
        final ArrayList<Integer> result = new ArrayList<Integer>();
        for (int i = 1; i <= this.degree; i++) {
            result.add(i);
            if (this.incremental) {
                result.add(-i);
            }
        }
        return result;
    }

    private GPOLO<BigIntImmutable> findOrder(final int degree,
        final CdpProblem cdp,
        final Set<Rule> usableRules,
        final Abortion aborter) throws AbortionException {
        final List<Citation> citations = Collections.singletonList(Citation.POLO);
        final ConstraintStuff cs = new ConstraintStuff(this.range, this.opcSolver, citations);

        final Set<OrderPolyConstraint<BigIntImmutable>> constraintSet =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();

        /* Interpret function symbols */
        {
            GInterpretationMode<BigIntImmutable> formDefined;
            if (degree > 0) {
                formDefined = new GInterpretationModeDegree<BigIntImmutable>(degree);
            } else {
                formDefined = new GInterpretationModeSimpleMixed<BigIntImmutable>(degree);
            }
            final LinkedHashSet<FunctionSymbol> definedSyms =
                new LinkedHashSet<FunctionSymbol>(cdp.getDefinedRSymbols());
            definedSyms.addAll(cdp.getDefinedPSymbols());
            final GInterpretationMode<BigIntImmutable> form =
                new GInterpretationModeDual<BigIntImmutable>(definedSyms,
                    new GInterpretationModeLinear<BigIntImmutable>(cs.boolRange, null), formDefined);

            final Set<FunctionSymbol> ruleSyms =
                aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(cdp.getR());
            final Set<FunctionSymbol> pairSyms =
                aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(cdp.getP());
            pairSyms.removeAll(ruleSyms);

            final Set<FunctionSymbol> constructorSyms = new LinkedHashSet<FunctionSymbol>(ruleSyms);
            constructorSyms.removeAll(cdp.getDefinedRSymbols());

            cs.gInterpretation.extend(cdp.getCompoundSymbols(), new GInterpretationModeStronglyLinear<BigIntImmutable>(
                ConstantPart.ZERO), aborter);
            cs.gInterpretation.extend(usableRules, form, aborter);
            cs.gInterpretation.extend(cdp.getP(), form, aborter);
        }

        /* Add constraints for pairs */
        {
            final Set<Constraint<TRSTerm>> pairTC = Constraint.fromRules(cdp.getP(), OrderRelation.GR);
            final Set<OrderPolyConstraint<BigIntImmutable>> pairOPCs =
                cs.gInterpretation.fromTermConstraints(pairTC, aborter);
            constraintSet.add(cs.commentedAnd("Pair constraints", pairOPCs));
        }

        /* Add usable rule constraints */
        {
            final Map<Rule, QActiveCondition> usableRulesMap =
                new LinkedHashMap<Rule, QActiveCondition>(usableRules.size());
            for (final Rule r : usableRules) {
                usableRulesMap.put(r, QActiveCondition.TRUE);
            }
            final OrderPolyConstraint<BigIntImmutable> usableRuleOPC =
                cs.gInterpretation.getActiveRuleConstraints(usableRulesMap, null, cs.boolRange, aborter);
            constraintSet.add(cs.constraintFactory.createComment("Usable rules constraints", usableRuleOPC));
        }

        OrderPolyConstraint<BigIntImmutable> finalConstraint = cs.constraintFactory.createAnd(constraintSet);
        finalConstraint = cs.constraintFactory.createQuantifierE(finalConstraint, finalConstraint.getFreeVariables());

        return cs.solveConstraint(finalConstraint, aborter);
    }

    static class CdpDirectComplexityProof extends Proof.DefaultProof {

        private final CdpProblem cdp;
        private final GPOLO<BigIntImmutable> order;
        private final Set<Rule> nonUsableRules;

        public CdpDirectComplexityProof(final GPOLO<BigIntImmutable> order, final CdpProblem cdp,
                final Set<Rule> nonUsableRules) {
            this.cdp = cdp;
            this.order = order;
            this.nonUsableRules = nonUsableRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final LinkedHashSet<Rule> usableRules = new LinkedHashSet<Rule>(this.cdp.getR());
            usableRules.removeAll(this.nonUsableRules);

            final StringBuilder sb = new StringBuilder();
            sb.append(o.escape("The following rules are not usable and may be omitted for the ordering:"));
            sb.append(o.newline());
            sb.append(o.set(this.nonUsableRules, Export_Util.RULES));
            sb.append(o.escape("Found linear/quadratic restricted ordering:"));
            sb.append(o.newline());
            sb.append(o.export(this.order));
            sb.append("Interpreted usable rules:");
            sb.append(o.set(this.format(o, usableRules), Export_Util.RULES));
            sb.append("Interpreted pairs:");
            sb.append(o.set(this.format(o, this.cdp.getP()), Export_Util.RULES));
            return sb.toString();
        }

        private Set<String> format(final Export_Util eu, final Set<Rule> rules) {
            final Set<String> formatted = new LinkedHashSet<String>();
            final GInterpretation<BigIntImmutable> interp = this.order.getInterpretation();
            try {
                // nasty, but don't want to make Proof.export(...)
                // throw AbortionException
                final Abortion dummyAborter = AbortionFactory.create();
                for (final Rule rule : rules) {
                    final OrderPoly<BigIntImmutable> lhsPoly = interp.interpretTerm(rule.getLeft(), dummyAborter);
                    final OrderPoly<BigIntImmutable> rhsPoly = interp.interpretTerm(rule.getRight(), dummyAborter);
                    final String lhsExport = lhsPoly.exportFlatDeep(interp.getFvInner(), interp.getFvOuter(), eu);
                    final String rhsExport = rhsPoly.exportFlatDeep(interp.getFvInner(), interp.getFvOuter(), eu);
                    formatted.add(rule + " : " + lhsExport + " " + eu.rightarrow() + " " + rhsExport);
                }
            } catch (final AbortionException e) {
                throw new RuntimeException(e);
            }
            // TODO Auto-generated method stub
            return formatted;
        }

    }

    public static class Arguments {
        public int range;
        /**
         * Must be positive integer
         */
        public int degree;

        /**
         * Stepwise increment the degree of the searched polynomial up to
         * <code>degree</code>.
         */
        public boolean incremental;

        /**
         * If incremental: Also try simple mixed polynomials.
         * If not incremental: Use simple mixed instead of "full" degree.
         */
        public boolean useSimpleMixed;

        public OPCSolver<BigIntImmutable> opcSolver;
        public boolean usableRules = true;
    }
}
