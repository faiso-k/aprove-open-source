package aprove.verification.complexity.CdtProblem.Processors;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.Implications.*;
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
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * RedPairP from Lars Noschinski's diploma thesis, but only for polynomial
 * orders.
 *
 * TODO: Generalize.
 */
public class CdtPolyRedPairProcessor extends CdtProblemProcessor {

    private final boolean findExp;
    private final int degree;
    private final OPCSolver<BigIntImmutable> opcSolver;
    private final int range;
    private final boolean allstrict;

    @ParamsViaArgumentObject
    public CdtPolyRedPairProcessor(final Arguments arguments) {
        this.findExp = arguments.findExp;
        this.degree = arguments.degree;
        this.opcSolver = arguments.opcSolver;
        this.range = arguments.range;
        this.allstrict = arguments.allstrict;
    }

    @Override
    protected boolean isCdtApplicable(final CdtProblem obl) {
        return true;
    }

    @SuppressWarnings("unused")
    @Override
    protected Result processCdt(final CdtProblem cdtProblem, final Abortion aborter)
            throws AbortionException {

        // FIXME: Implement active conditions for CdtProblems, then replace this hack
        // with QTRSProblem.
        final QTRSProblem qtrs = QTRSProblem.create(cdtProblem.getR()).createInnermost();
        final QUsableRules quc = new QUsableRules(qtrs);

        final State st = new State(cdtProblem,
                new ConstraintStuff(this.range, this.opcSolver, Collections.<Citation>emptyList()));

        final GPOLO<BigIntImmutable> order =
            this.findOrdering(cdtProblem, st, this.degree, quc, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful("Could not find a suitable reduction pair");
        }

        // henceforth, order != null!
        final Set<Rule> usableRules = new HashSet<Rule>();
        for (final Map.Entry<Rule, QActiveCondition> entry : quc.getActiveConditions(st.tupleRules, false).entrySet()) {
            if (order.checkQActiveCondition(entry.getValue())) {
                usableRules.add(entry.getKey());
            }
        }

        if (Globals.DEBUG_NOSCHINSKI) {
            final GInterpretation<BigIntImmutable> interp = order.getInterpretation();
            System.err.println("---- RULE INTERP ----");
            for (final Rule r : st.rules) {
                System.err.println(r + ": " + CdtPolyRedPairProcessor.niceInterpretRule(st.cs, interp, r, aborter));
            }
            System.err.println("---- TUPLE INTERP ----");
            for (final Rule r : st.tupleRules) {
                System.err.println(r + ": " + CdtPolyRedPairProcessor.niceInterpretRule(st.cs, interp, r, aborter));
            }
        }

        SanityChecks.flatten(order.getInterpretation());

        /* find strict tuples */
        final Set<Cdt> strictTuples = new LinkedHashSet<Cdt>();
        for (final Cdt cdt : cdtProblem.getTuples()) {
            // TODO: Extend this, so we can detect if tuples neither in K
            // or S can be added to K.
            if (!cdtProblem.getS().contains(cdt)) {
                continue;
            }

            final Rule cdtRule = cdt.getRule();
            if (order.inRelation(cdtRule.getLeft(), cdtRule.getRight())) {
                strictTuples.add(cdt);
            } else if (Globals.useAssertions) {
                // if the order does not recognize it as strict, then the
                // constraint solver should not consider it as strict either!
                final GPolyVar var =  st.tupleStrictGPolyVars.get(cdt);
                final BigIntImmutable val = st.cs.solution.get(var);
                assert val.equals(BigIntImmutable.ZERO) : val;

                // and the rule should have been oriented at least weakly, then
                final Constraint<TRSTerm> c = Constraint.fromRule(cdtRule, OrderRelation.GE);
                assert order.solves(c);
            }
        }

        if (Globals.useAssertions) {
            this.assertCorrectness(cdtProblem, st, order, strictTuples);
        }

        final LinkedHashSet<Cdt> newS = new LinkedHashSet<Cdt>(cdtProblem.getS());
        newS.removeAll(strictTuples);
        final LinkedHashSet<Cdt> newK = new LinkedHashSet<Cdt>(cdtProblem.getK());
        newK.addAll(strictTuples);
        final CdtProblem newCdtProblem = cdtProblem.createSubproblem(
                cdtProblem.getGraph(),
                ImmutableCreator.create(newS),
                ImmutableCreator.create(newK));

        final ComplexityValue upperBound;
        if (this.findExp) {
            upperBound = ComplexityValue.exponential();
        }
        else {
            // Extract degree from the interpretation that was actually found
            // (may be smaller than the highest degree considered for the
            // search)
            final BigInteger realDegree = order.getInterpretation().getDegree();
            final int intRealDegree = realDegree.intValue();
            if (Globals.useAssertions) {
                assert realDegree.compareTo(BigInteger.valueOf(Math.abs(this.degree))) <= 0;
                assert realDegree.equals(BigInteger.valueOf(intRealDegree));
            }
            upperBound = ComplexityValue.fixedDegreePoly(intRealDegree);
        }
        return ResultFactory.proved(
                newCdtProblem,
                UpperBound.create(new SumComputation(upperBound)),
            new CdtRuleRemovalProof(order, cdtProblem.getTuples(), strictTuples, usableRules));
    }

    /**
     *
     * @param cdtProblem
     * @param st
     * @param order - its interpretation must have been flattened!
     * @param strictTuples
     */
    private void assertCorrectness(final CdtProblem cdtProblem, final State st,
            final GPOLO<BigIntImmutable> order, final Set<Cdt> strictTuples) {
        final GInterpretation<BigIntImmutable> interp = order.getInterpretation();
        //SanityChecks.flatten(interp);
        final LinkedHashSet<FunctionSymbol> nonConstructors =
            new LinkedHashSet<FunctionSymbol>(cdtProblem.getDefinedPSymbols());
        nonConstructors.addAll(cdtProblem.getDefinedRSymbols());
        assert(this.findExp || SanityChecks.constructorSymbolsStronglyLinear(
                interp, nonConstructors, true));
        assert(!strictTuples.isEmpty());
    }

    private GPOLO<BigIntImmutable> findOrdering(final CdtProblem cdtProblem,
            final State st, final int degree, final QUsableRules quc, final Abortion aborter)
            throws AbortionException {
        final GInterpretation<BigIntImmutable> interp = st.cs.gInterpretation;

        final Set<OrderPolyConstraint<BigIntImmutable>> constraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();

        st.tupleRules = new LinkedHashSet<Rule>();
        for (final Cdt cdt : cdtProblem.getTuples()) {
            st.tupleRules.add(cdt.getRule());
        }

        { /* Interpret compound symbols as sum of their arguments */
            final GInterpretationMode<BigIntImmutable> sli = new GInterpretationModeStronglyLinear<BigIntImmutable>(ConstantPart.ZERO);
            for (final Cdt cdt : cdtProblem.getTuples()) {
                interp.extend(cdt.getCompoundSym(), sli, aborter);
            }
        }

        st.usableRules = new ImmutableRuleSet<Rule>(quc.getUsableRules(st.tupleRules));

        {
            final GInterpretationMode<BigIntImmutable> form =
                new GInterpretationModeDegree<BigIntImmutable>(degree);
            this.interpretFunctionSymbols(st, form, cdtProblem, aborter);
        }

        {
            final Set<OrderPolyConstraint<BigIntImmutable>> tupleConstraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
            final List<OrderPoly<BigIntImmutable>> tupleStrictVars =
                new ArrayList<OrderPoly<BigIntImmutable>>();
            for (final Cdt tuple : cdtProblem.getTuples()) {
                final Rule tupleRule = tuple.getRule();
                if (cdtProblem.getS().contains(tuple)) {
                    if (this.allstrict) {
                        tupleConstraints.add(interp.getPolynomialConstraint(tupleRule,
                            ConstraintType.GT, aborter));
                    }
                    final GPolyVar tmp = st.cs.gInterpretation.getNextCoeff("ts_", st.cs.boolRange);
                    st.tupleStrictGPolyVars.put(tuple, tmp);
                    final OrderPoly<BigIntImmutable> tupleStrictVar =
                        st.cs.makeOrderPolyFromVar(tmp);
                    tupleStrictVars.add(tupleStrictVar);

                    tupleConstraints.add(st.cs.geConstraint(
                            interp.interpretTerm(tupleRule.getLeft(), aborter),
                            st.cs.orderPolyFactory.plus(
                                    tupleStrictVar,
                                    interp.interpretTerm(tupleRule.getRight(), aborter)
                                    )
                            ));
                } else {
                    tupleConstraints.add(interp.getPolynomialConstraint(tupleRule, ConstraintType.GE,
                            aborter));
                }
            }

            /*
             * At least one tuple must be strict: sum of the tupleStrictVars
             * must be greater then 0
             */
            {
                /*
                 * There is at least one element in S, as processCdt() is only
                 * called if S is not empty. Hence tupleStrictVars is not empty.
                 */
                OrderPoly<BigIntImmutable> tsvSum = tupleStrictVars.get(0);
                final int size = tupleStrictVars.size();
                for (int i=1; i < size; i++) {
                    tsvSum = st.cs.orderPolyFactory.plus(tsvSum, tupleStrictVars.get(i));
                }
                tupleConstraints.add(st.cs.gtConstraint(tsvSum, st.cs.orderPolyFactory.getZero()));
            }
            constraints.add(st.cs.commentedAnd("Tuples", tupleConstraints));
        }

        /* Add usable rules constraints */
        final Map<QActiveCondition, GPolyVar> qacCache =
            new LinkedHashMap<QActiveCondition, GPolyVar>();
        final Set<Rule> pairsAndRules = new LinkedHashSet<Rule>(st.usableRules);
        pairsAndRules.addAll(st.tupleRules);
        final Map<Rule, QActiveCondition> qacMap = quc.getActiveConditions(pairsAndRules);

        final Map<Rule, OrderPoly<BigIntImmutable>> qacVarMap =
            new LinkedHashMap<Rule, OrderPoly<BigIntImmutable>>(qacMap.size());

        {
            final Set<OrderPolyConstraint<BigIntImmutable>> activeConstraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();

            for (final Map.Entry<Rule, QActiveCondition> e : qacMap.entrySet()) {
                final Set<OrderPolyConstraint<BigIntImmutable>> ruleActiveConstraints =
                    new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
                final GPoly<BigIntImmutable, GPolyVar> activeConditionVar =
                    interp.getActiveCondition(e.getValue(), ruleActiveConstraints,
                            qacCache, st.cs.boolRange, aborter);
                activeConstraints.add(
                        st.cs.commentedAnd(
                                "Active Constraints for " + e,
                                ruleActiveConstraints));
                qacVarMap.put(
                        e.getKey(),
                        st.cs.orderPolyFactory.buildFromCoeff(activeConditionVar));
            }

            constraints.add(
                    st.cs.commentedAnd("Active Constraints", activeConstraints));
        }

        // Create constraint
        // (pPos /\ Uactive(R|pos) in >=) \/ (... /\ U(R|pos) in >)
        final Set<OrderPolyConstraint<BigIntImmutable>> activeUsableRulesConstraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        for (final Cdt cdt : cdtProblem.getTuples()) {
            final TRSFunctionApplication pairLhs = cdt.getRuleLHS();
            for (int i=0; i < cdt.getRuleRHSArgs().size(); i++) {

                final Set<Rule> usableRules = quc.getUsableRules(
                        Rule.create(pairLhs, cdt.getRuleRHSArgs().get(i)));

                for (final Rule usableRule : usableRules) {
                    OrderPolyConstraint<BigIntImmutable> constraint =
                        st.cs.condGeConstraint(
                                qacVarMap.get(usableRule),
                                interp.interpretTerm(usableRule.getLeft(), aborter),
                                interp.interpretTerm(usableRule.getRight(), aborter)
                                );
                    constraint = st.cs.constraintFactory.createComment(usableRule.toString(), constraint);
                   activeUsableRulesConstraints.add(constraint);
                }
            }
        }
        constraints.add(st.cs.commentedAnd(
                "Active usable rules constraints",
                activeUsableRulesConstraints));

        /* Solve constraint */
        OrderPolyConstraint<BigIntImmutable> constraint =
            st.cs.constraintFactory.createAnd(constraints);
        constraint = st.cs.constraintFactory.createQuantifierE(
                constraint, constraint.getFreeVariables());

        if ( Globals.DEBUG_NOSCHINSKI) {
            final OPCExportVisitor<BigIntImmutable> export = new OPCExportVisitor<BigIntImmutable>(st.cs.fvInner, st.cs.fvOuter, new PLAIN_Util());
            export.applyTo(constraint);
            System.err.println(new PLAIN_Util().set(st.rules, Export_Util.RULES));
            System.err.println(new PLAIN_Util().set(st.tupleRules, Export_Util.RULES));
            System.err.println(interp);
            System.err.println(export);
        }
        return st.cs.solveConstraint(constraint, aborter);
    }

    private static String niceInterpretRule(final ConstraintStuff cs,
            final GInterpretation<BigIntImmutable> interp, final Rule r,
            final Abortion aborter) throws AbortionException {
        final PLAIN_Util eu = new PLAIN_Util();
        final OrderPoly<BigIntImmutable> lhsI = interp.interpretTerm(r.getLeft(), aborter);
        final OrderPoly<BigIntImmutable> rhsI = interp.interpretTerm(r.getRight(), aborter);
        return lhsI.exportFlatDeep(cs.fvInner, cs.fvOuter, eu) +
                " >?> " + rhsI.exportFlatDeep(cs.fvInner, cs.fvOuter, eu);
    }

    /**
     * Interprets function symbols (and their pair versions). Fills
     * the fsToPs field of st.
     */
    private void interpretFunctionSymbols(final State st,
            final GInterpretationMode<BigIntImmutable> form, final CdtProblem cdtProblem,
            final Abortion aborter) throws AbortionException {

        final GInterpretationMode<BigIntImmutable> constantForm = (this.findExp
                ? new GInterpretationModeLinear<BigIntImmutable>()
                : new GInterpretationModeLinear<BigIntImmutable>(st.cs.boolRange, null));

        final Set<FunctionSymbol> occuringSyms =
            aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(st.usableRules);
        occuringSyms.addAll(
                aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(st.tupleRules));

        final Set<FunctionSymbol> defSyms =
            new LinkedHashSet<FunctionSymbol>(cdtProblem.getDefinedRSymbols());
        defSyms.addAll(cdtProblem.getDefinedPSymbols());
        defSyms.retainAll(occuringSyms);

        for (final FunctionSymbol fs : defSyms) {
            st.cs.gInterpretation.extend(fs, form, aborter);
        }

        occuringSyms.removeAll(defSyms);
        for (final FunctionSymbol fs : occuringSyms) {
            st.cs.gInterpretation.extend(fs, constantForm, aborter);
        }
    }

    private static class State {
        public final ImmutableRuleSet<Rule> rules;
        public final ImmutableSet<FunctionSymbol> signature;
        public final ConstraintStuff cs;

        public Set<Rule> usableRules;
        public Set<Rule> tupleRules;
        public final Map<Cdt, GPolyVar> tupleStrictGPolyVars =
            new LinkedHashMap<Cdt, GPolyVar>();

        public State(final CdtProblem cdtProblem, final ConstraintStuff cs) {
            this.cs = cs;

            this.rules = new ImmutableRuleSet<Rule>(cdtProblem.getR());
            this.signature = cdtProblem.getSignature();
            new FreshNameGenerator(this.signature, FreshNameGenerator.APPEND_NUMBERS);
        }
    }

    public static class CdtRuleRemovalProof extends CpxProof {

        private final ExportableOrder<TRSTerm> order;
        private final Set<Cdt> tuples;
        private final Set<Cdt> strict;
        private final Set<Rule> usableRules;

        public CdtRuleRemovalProof(
            final ExportableOrder<TRSTerm> order,
            final Set<Cdt> tuples,
            final Set<Cdt> strict,
            final Set<Rule> usableRules)
        {
            this.order = order;
            this.tuples = tuples;
            this.strict = strict;
            this.usableRules = usableRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append(o.escape("Found a reduction pair which oriented the following tuples strictly. Hence they can be removed from S."));
            sb.append(o.set(this.strict, Export_Util.RULES));
            sb.append(o.escape("We considered the (Usable) Rules:"));
            sb.append(o.set(this.usableRules, Export_Util.RULES));
            sb.append(o.escape("And the Tuples:"));
            sb.append(o.set(this.tuples, Export_Util.RULES));
            sb.append(o.escape("The order we found is given by the following interpretation:"));
            sb.append(o.newline());
            sb.append(o.export(this.order));
            return sb.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            final Element res = CPFTag.RULE_SHIFTING.create(doc);
            res.appendChild(this.order.toCPF(doc, xmlMetaData));
            final Element rules = CPFTag.RULES.create(doc);
            for (final Cdt cdt : this.strict) {
                rules.appendChild(cdt.toCPF(doc, xmlMetaData));
            }
            res.appendChild(CPFTag.TRS.create(doc, rules));
            final Element ur = CPFTag.RULES.create(doc);
            for (final Cdt cdt : this.tuples) {
                ur.appendChild(cdt.toCPF(doc, xmlMetaData));
            }
            for (final Rule rule : this.usableRules) {
                ur.appendChild(rule.toCPF(doc, xmlMetaData));
            }
            res.appendChild(CPFTag.USABLE_RULES.create(doc, ur));
            res.appendChild(childrenProofs[0]);
            return this.positiveTag().create(doc, res);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }
    }

    public static class Arguments {
        /**
         * Search for orders which guarantee exponential upper bounds
         */
        public boolean findExp = false;
        public int range;
        public OPCSolver<BigIntImmutable> opcSolver;
        public int degree;
        public boolean allstrict = false;
    }
}
