package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Computes an upper bound for the complexity of an {@link RuntimeComplexityTrsProblem}
 * using the generalized Cdp method.
 *
 * XXX: Documentation. No written down theory yet.
 */
public class CpxTrsDirectGcdpComplexityProcessor extends RuntimeComplexityTrsProcessor {

    private final AdditionalRestrictions additionalRestrictions;
    private final int degree;
    private final OPCSolver<BigIntImmutable> opcSolver;
    private final int range;

    @ParamsViaArgumentObject
    public CpxTrsDirectGcdpComplexityProcessor(final Arguments arguments) {
        this.degree = arguments.degree;
        this.opcSolver = arguments.opcSolver;
        this.range = arguments.range;
        this.additionalRestrictions = arguments.additionalRestrictions;
    }

    @Override
    public boolean isRuntimeComplexityTrsApplicable(final RuntimeComplexityTrsProblem cpx) {
        return cpx.getRewriteStrategy() == RewriteStrategy.INNERMOST;
    }

    @Override
    public Result processRuntimeComplexityTrs(final RuntimeComplexityTrsProblem obl, final Abortion aborter) throws AbortionException {
        final RuntimeComplexityTrsProblem cpx = obl;

        final State st = new State(cpx,
                new ConstraintStuff(this.range, this.opcSolver, Collections.<Citation>emptyList()));
        st.additionalRestrictions = this.additionalRestrictions;

        final GPOLO<BigIntImmutable> order =
            CpxTrsDirectGcdpComplexityProcessor.findOrdering(cpx, st, this.degree, aborter);

        if (Globals.useAssertions && order != null) {
            final GInterpretation<BigIntImmutable> interp = order.getInterpretation();
            SanityChecks.flatten(interp);
            final LinkedHashSet<FunctionSymbol> definedSymbols =
                new LinkedHashSet<FunctionSymbol>(st.definedSyms);
            definedSymbols.addAll(st.fsToPs.values());
            assert(SanityChecks.constructorSymbolsStronglyLinear(
                    interp, definedSymbols, true));

            final LinkedHashMap<FunctionSymbol, BitSet> monotonicityRequirements =
                new LinkedHashMap<FunctionSymbol, BitSet>();
            for (final Map.Entry<FunctionSymbol, List<OrderPoly<BigIntImmutable>>> mcv
                    : st.monotonicityConstraintVars.entrySet()) {
                final FunctionSymbol fs = mcv.getKey();
                final BitSet monArgs = new BitSet(fs .getArity());

                int i = 0;
                for (final OrderPoly<BigIntImmutable> monPoly : mcv.getValue()) {
                    /* monPoly just wraps a GPolyVar */
                    final GPolyVar var =  monPoly.getInnerVariables().iterator().next();
                    final BigIntImmutable val = st.cs.solution.get(var);
                    if (val.equals(BigIntImmutable.ONE)) {
                        monArgs.set(i);
                    }

                    i++;
                }
                if (!monArgs.isEmpty()) {
                    monotonicityRequirements.put(fs, monArgs);
                }
            }
            assert(SanityChecks.isStronglyMonotone(
                    interp, monotonicityRequirements));
        }

        if (order != null) {
            return ResultFactory.provedWithValue(
                    ComplexityYNM.createUpper(ComplexityValue.fixedDegreePoly(Math.abs(this.degree))),
                    new QtrsDirectGcdpComplexityProof(order, st));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private static GPOLO<BigIntImmutable> findOrdering(final RuntimeComplexityTrsProblem cpx,
            final State st, final int degree,final Abortion aborter)
            throws AbortionException {
        final GInterpretation<BigIntImmutable> interp = st.cs.gInterpretation;

        final Set<OrderPolyConstraint<BigIntImmutable>> constraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();

        final FunctionSymbol compound_0 =
            CpxTrsDirectGcdpComplexityProcessor.freshFunctionSymbol(st.fng, "c", 0);
        final FunctionSymbol compound_1 =
            CpxTrsDirectGcdpComplexityProcessor.freshFunctionSymbol(st.fng, "c", 1);

        CpxTrsDirectGcdpComplexityProcessor.generatePairSymbols(st);
        st.pairs = new LinkedHashSet<Rule>(st.rules.size());

        final Map<Rule, List<OrderPoly<BigIntImmutable>>> pair2relPosVars =
            new LinkedHashMap<Rule, List<OrderPoly<BigIntImmutable>>>(st.rules.size());
        final Map<Rule, ArrayList<Integer>> pair2pairPosDependencies =
            new LinkedHashMap<Rule, ArrayList<Integer>>(st.rules.size());
        final Map<Rule, DefinedPositionsTree> pair2dpt =
            new LinkedHashMap<Rule, DefinedPositionsTree>(st.rules.size());
        /* Add constraints for pair rules*/
        {
            for (final Rule rule : st.rules) {
                final TRSFunctionApplication pLhs = CpxTrsDirectGcdpComplexityProcessor.makePairTerm(st, rule.getLeft());

                final DefinedPositionsTree dpt = DefinedPositionsTree.create(
                        rule.getRight(), st.definedSyms);

                final ArrayList<TRSFunctionApplication> definedSubterms =
                    new ArrayList<TRSFunctionApplication>();
                final ArrayList<TRSFunctionApplication> definedPairSubterms =
                    new ArrayList<TRSFunctionApplication>();
                final ArrayList<Integer> pairPosVarDependencies =
                    new ArrayList<Integer>();
                final ArrayList<DefinedPositionsTree> dpts =
                    new ArrayList<DefinedPositionsTree>();

                {
                    final Queue<Pair<Integer,DefinedPositionsTree>> treeQueue =
                        new ArrayDeque<Pair<Integer,DefinedPositionsTree>>();
                    treeQueue.add(new Pair<Integer, DefinedPositionsTree>(-1, dpt));
                    int i = -1;
                    while (!treeQueue.isEmpty()) {
                        final Pair<Integer, DefinedPositionsTree> top = treeQueue.poll();
                        if (top.y.t != null) {
                            pairPosVarDependencies.add(top.x);
                            definedSubterms.add(top.y.t);
                            definedPairSubterms.add(CpxTrsDirectGcdpComplexityProcessor.makePairTerm(st, top.y.t));
                            dpts.add(top.y);
                            i++;
                        }
                        for (final DefinedPositionsTree subDpt : top.y.sub) {
                            treeQueue.add(new Pair<Integer, DefinedPositionsTree>(i, subDpt));
                        }
                    }

                    if (Globals.useAssertions) {
                        assert i == -1 || (i+1 == pairPosVarDependencies.size() && i+1 == definedPairSubterms.size());
                    }
                }

                FunctionSymbol compound;
                if (definedPairSubterms.size() == 0) {
                    compound = compound_0;
                } else if (definedPairSubterms.size() == 1){
                    compound = compound_1;
                } else {
                    compound = CpxTrsDirectGcdpComplexityProcessor.freshFunctionSymbol(st.fng, "c", definedPairSubterms.size());
                }
                final TRSFunctionApplication pRhs =
                    TRSTerm.createFunctionApplication(compound, definedPairSubterms);
                final Rule pRule = Rule.create(pLhs, pRhs);
                st.pairs.add(pRule);

                final Pair<OrderPoly<BigIntImmutable>, List<OrderPoly<BigIntImmutable>>> compoundInterp =
                    CpxTrsDirectGcdpComplexityProcessor.interpretCompoundSymbol(st.cs, compound);
                interp.extend(compound,
                        compoundInterp.x, aborter);
                final List<OrderPoly<BigIntImmutable>> relPosVars = compoundInterp.y;

                pair2dpt.put(pRule, dpt);
                pair2relPosVars.put(pRule, relPosVars);
                pair2pairPosDependencies.put(pRule, pairPosVarDependencies);

                for (int i=0; i < relPosVars.size(); i++) {
                    dpts.get(i).pairPosVar = relPosVars.get(i);
                }
            }
        }

        final QTRSProblem qtrs = QTRSProblem.create(cpx.getR()).createInnermost();
        final QUsableRules quc = new QUsableRules(qtrs);
        st.usableRules = new ImmutableRuleSet<Rule>(quc.getUsableRules(st.pairs));

        {
            final GInterpretationMode<BigIntImmutable> form =
                new GInterpretationModeDegree<BigIntImmutable>(degree);
            CpxTrsDirectGcdpComplexityProcessor.interpretFunctionSymbols(st, form, cpx, aborter);
        }

        {
            final Set<OrderPolyConstraint<BigIntImmutable>> pairConstraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>(st.pairs.size());
            for (final Rule pair : st.pairs) {
                pairConstraints.add(interp.getPolynomialConstraint(pair, ConstraintType.GT,
                        aborter));
            }
            constraints.add(st.cs.commentedAnd("Pairs", pairConstraints));
        }

        {
            final Set<OrderPolyConstraint<BigIntImmutable>> relPosVarConstraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>(st.rules.size());;
            for (final Rule pair : st.pairs) {
                final ArrayList<Integer> pairPosDependencies =
                    pair2pairPosDependencies.get(pair);
                final List<OrderPoly<BigIntImmutable>> relPosVars =
                    pair2relPosVars.get(pair);
                relPosVarConstraints.add(
                        CpxTrsDirectGcdpComplexityProcessor.computeConstraintsOnRelPosVars(st, pairPosDependencies, relPosVars));
            }
            constraints.add(st.cs.commentedAnd("RelPosVars", relPosVarConstraints));
        }



        st.ruleIsStrictVars =
            new LinkedHashMap<Rule, OrderPoly<BigIntImmutable>>(st.usableRules.size());
        for (final Rule rule : st.usableRules) {
            final GPolyVar coeffVar =
                st.cs.gInterpretation.getNextCoeff(
                        "str_" , st.cs.boolRange);

            st.ruleIsStrictVars.put(rule, st.cs.makeOrderPolyFromVar(coeffVar));
        }

        /* Add strong monotonicity constraints */
        {
            final Set<OrderPolyConstraint<BigIntImmutable>> monotonicityConstraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
            final Set<FunctionSymbol> allSyms =
                new LinkedHashSet<FunctionSymbol>(st.signature);
            allSyms.addAll(aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(st.pairs));
            for(final FunctionSymbol fs : allSyms) {
                if (interp.getPol().get(fs) == null) {
                    continue;
                }
                final List<OrderPoly<BigIntImmutable>> monConstVars =
                    BigIntImmutableRing.getStrongMonotonicityConstraints(
                            interp, fs, monotonicityConstraints, st.cs.boolRange);
                st.monotonicityConstraintVars.put(fs, monConstVars);
            }
            constraints.add(st.cs.commentedAnd(
                    "Monotonicity Constraints", monotonicityConstraints));
        }

        /* Compute strong monotonicity requirements */
        {
            final Set<OrderPolyConstraint<BigIntImmutable>> monReq1Constraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
            final Set<OrderPolyConstraint<BigIntImmutable>> monReq2Constraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
            CpxTrsDirectGcdpComplexityProcessor.computeMonotonicityRequirements1(st, monReq1Constraints);
            for (final Rule pair : st.pairs) {
                final DefinedPositionsTree dpt = pair2dpt.get(pair);
                CpxTrsDirectGcdpComplexityProcessor.computeMonotonicityRequirements2(dpt, st, monReq2Constraints);
            }
            constraints.add(st.cs.commentedAnd(
                    "Monotonicity Requirements 1", monReq1Constraints));
            constraints.add(st.cs.commentedAnd(
                    "Monotonicity Requirements 2", monReq2Constraints));
        }


        /* Add usable rules constraints */
        final Map<QActiveCondition, GPolyVar> qacCache =
            new LinkedHashMap<QActiveCondition, GPolyVar>();
        final Set<Rule> pairsAndRules = new LinkedHashSet<Rule>(st.usableRules);
        pairsAndRules.addAll(st.pairs);
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
        final Set<OrderPolyConstraint<BigIntImmutable>> oneMinusRpvVars =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>(st.rules.size());
        final Set<OrderPolyConstraint<BigIntImmutable>> activeUsableRulesConstraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        final Set<OrderPolyConstraint<BigIntImmutable>> usableRulesConstraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        final Set<OrderPolyConstraint<BigIntImmutable>> usableRulesStrictnessConstraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        for (final Rule pair : st.pairs) {
            final List<OrderPoly<BigIntImmutable>>relPosVars =
                pair2relPosVars.get(pair);
            final ArrayList<Integer> dependencies =
                pair2pairPosDependencies.get(pair);
            int i = 0;
            final TRSFunctionApplication pairRhs = (TRSFunctionApplication) pair.getRight();
            final TRSFunctionApplication pairLhs = pair.getLeft();
            for (final TRSTerm t: pairRhs.getArguments()) {
                final TRSFunctionApplication subterm = (TRSFunctionApplication) t;

                final boolean topmost = dependencies.get(i) == -1;

                final OrderPoly<BigIntImmutable> relPosVar =
                    relPosVars.get(i);

                i++;

                if (topmost) {
                    continue;
                }

                final Set<Rule> usableRules = quc.getUsableRules(
                        Rule.create(pairLhs, CpxTrsDirectGcdpComplexityProcessor.makeRuleTerm(st, subterm)));

                /* A pair is used for this position */
                for (final Rule usableRule : usableRules) {
                    OrderPolyConstraint<BigIntImmutable> constraint =
                        st.cs.condGeConstraint(
                                st.cs.orderPolyFactory.times(
                                        qacVarMap.get(usableRule),
                                        relPosVar),
                                interp.interpretTerm(usableRule.getLeft(), aborter),
                                interp.interpretTerm(usableRule.getRight(), aborter));
                    constraint = st.cs.constraintFactory.createComment(usableRule.toString(), constraint);
                    activeUsableRulesConstraints.add(constraint);
                }

                /* No pair is used for this position */
                // XXX: move monotonicity constraints here
                final OrderPoly<BigIntImmutable> oneMinusRpv =
                    st.cs.makeOrderPolyFromVar(interp.getNextCoeff(
                            "omr", st.cs.boolRange));
                oneMinusRpvVars.add(
                        st.cs.eqConstraint(
                                st.cs.orderPolyFactory.minus(
                                        st.cs.orderPolyFactory.getOne(),
                                        oneMinusRpv),
                                relPosVar)
                );

                for (final Rule usableRule : usableRules) {
                    usableRulesConstraints.add(st.cs.condGtConstraint(
                            oneMinusRpv,
                            interp.interpretTerm(usableRule.getLeft(), aborter),
                            interp.interpretTerm(usableRule.getRight(), aborter)));

                    usableRulesStrictnessConstraints.add(
                            st.cs.geConstraint(
                                    st.ruleIsStrictVars.get(usableRule),
                                    oneMinusRpv)
                            );
                }
            }
        }
        constraints.add(st.cs.commentedAnd(
                "Active usable rules constraints",
                activeUsableRulesConstraints));
        constraints.add(
                st.cs.commentedAnd(
                        "Usable Rules constraints",
                        usableRulesConstraints));
        constraints.add(
                st.cs.commentedAnd(
                        "Usable Rules strictness constraints",
                        usableRulesStrictnessConstraints));

        constraints.add(
                st.cs.commentedAnd(
                        "One-Minus-RelPosVar variables",
                        oneMinusRpvVars));

        /* Solve constraint */
        OrderPolyConstraint<BigIntImmutable> constraint =
            st.cs.constraintFactory.createAnd(constraints);
        constraint = st.cs.constraintFactory.createQuantifierE(
                constraint, constraint.getFreeVariables());

        if (Globals.DEBUG_NOSCHINSKI) {
            final OPCExportVisitor<BigIntImmutable> export = new OPCExportVisitor<BigIntImmutable>(st.cs.fvInner, st.cs.fvOuter, new PLAIN_Util());
            export.applyTo(constraint);
            System.err.println(new PLAIN_Util().set(st.rules, Export_Util.RULES));
            System.err.println(new PLAIN_Util().set(st.pairs, Export_Util.RULES));
            System.err.println(st.ruleIsStrictVars);
            System.err.println(interp);
            System.err.println(export);
        }
        return st.cs.solveConstraint(constraint, aborter);
    }

    /**
     * Replaces the outer function symbol by its pair function symbol
     */
    private static TRSFunctionApplication makePairTerm(final State st, final TRSFunctionApplication fa) {
        return TRSTerm.createFunctionApplication(
                st.fsToPs.get(fa.getRootSymbol()),
                fa.getArguments());
    }

    /**
     * Replaces the outer pair symbol by its function symbol
     */
    private static TRSFunctionApplication makeRuleTerm(final State st, final TRSFunctionApplication fa) {
        return TRSTerm.createFunctionApplication(
                st.psToFs.get(fa.getRootSymbol()),
                fa.getArguments());
    }

    /**
     * Restricts the possible values for relPosVars, i.e. for the coefficients
     * in the interpretation of compound symbols.
     */
    private static OrderPolyConstraint<BigIntImmutable> computeConstraintsOnRelPosVars(
            final State st, final ArrayList<Integer> pairPosVarDependencies,
            final List<OrderPoly<BigIntImmutable>> relPosVars) {
        final Set<OrderPolyConstraint<BigIntImmutable>> constraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        final OrderPoly<BigIntImmutable> wdpOrCdpVar =
            st.cs.orderPolyFactory.buildFromInnerVariable(
                    st.cs.gInterpretation.getNextCoeff("wc", st.cs.boolRange));
        for (int i = 0; i < pairPosVarDependencies.size(); i++) {
            final int parentOfI = pairPosVarDependencies.get(i);
            final OrderPoly<BigIntImmutable> rpv = relPosVars.get(i);
            if (parentOfI == -1) { // topmost position
                // All topmost defined terms have relPosVar = 1
                constraints.add(st.cs.eqConstraint(rpv, st.cs.orderPolyFactory.getOne()));
            } else if (st.additionalRestrictions == AdditionalRestrictions.LikeWdp) {
                constraints.add(st.cs.eqConstraint(rpv, st.cs.orderPolyFactory.getZero()));
            } else if (st.additionalRestrictions == AdditionalRestrictions.LikeCdp) {
                constraints.add(st.cs.eqConstraint(rpv, st.cs.orderPolyFactory.getOne()));
            } else if (st.additionalRestrictions == AdditionalRestrictions.EachPairLikeWdpOrCdp) {
                constraints.add(st.cs.eqConstraint(rpv, wdpOrCdpVar));
            } else { // term on position i depends on term on position parentOfI
                // if relPosVar=0 for one position then
                // relPosVar=0 for all positions below.
                final OrderPoly<BigIntImmutable> parentVar =
                    relPosVars.get(parentOfI);
                constraints.add(st.cs.geConstraint(parentVar, rpv));
            }
        }
        return st.cs.constraintFactory.createAnd(constraints);
    }

    /**
     * Interprets function symbols (and their pair versions). Fills
     * the fsToPs field of st.
     */
    private static void interpretFunctionSymbols(final State st,
            final GInterpretationMode<BigIntImmutable> form, final RuntimeComplexityTrsProblem cpx,
            final Abortion aborter) throws AbortionException {

        final GInterpretationMode<BigIntImmutable> constantForm =
            new GInterpretationModeLinear<BigIntImmutable>(st.cs.boolRange, null);

        final Set<FunctionSymbol> occuringSyms =
            aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(st.usableRules);
        occuringSyms.addAll(
                aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(st.pairs));

        final Set<FunctionSymbol> defSyms = new LinkedHashSet<FunctionSymbol>(st.definedSyms);
        defSyms.addAll(st.fsToPs.values());
        defSyms.retainAll(occuringSyms);

        for (final FunctionSymbol fs : defSyms) {
            st.cs.gInterpretation.extend(fs, form, aborter);
        }

        occuringSyms.removeAll(defSyms);
        for (final FunctionSymbol fs : occuringSyms) {
            st.cs.gInterpretation.extend(fs, constantForm, aborter);
        }
    }

    private static void generatePairSymbols(final State st) {
        for (final FunctionSymbol fs : st.signature) {
            final String pairSymbolName =
                st.fng.getFreshName(fs.getName(), true, FreshNameGenerator.DEPENDENCY_PAIRS);
            final FunctionSymbol pairSymbol =
                FunctionSymbol.create(pairSymbolName, fs.getArity());
            st.addMappingFsToPs(fs, pairSymbol);
        }
    }
    /**
     * @return The interpretation of <code>fs</code> and the list of
     *         coefficients of the arguments.
     */
    private static Pair<OrderPoly<BigIntImmutable>,List<OrderPoly<BigIntImmutable>>> interpretCompoundSymbol(
            final ConstraintStuff cs,
            final FunctionSymbol fs) {
        final GInterpretation<BigIntImmutable> interp = cs.gInterpretation;
        OrderPoly<BigIntImmutable> inter = cs.orderPolyFactory.getZero();

        final int arity = fs.getArity();
        final ArrayList<OrderPoly<BigIntImmutable>> coeffs =
            new ArrayList<OrderPoly<BigIntImmutable>>(arity);

        for (int i=0; i < arity; i++) {
            final GPolyVar coeffVar =
                interp.getNextCoeff("pp." + fs.getName() +"." + fs.getArity() + "." + i + "_", cs.boolRange);
            final OrderPoly<BigIntImmutable> coeff = cs.makeOrderPolyFromVar(coeffVar);
            coeffs.add(coeff);
            final OrderPoly<BigIntImmutable> var =
                cs.orderPolyFactory.buildFromVariable(interp.getVariableForFunctionSymbolArgument(i));
            inter = interp.getFactory().plus(inter,
                    interp.getFactory().times(coeff, var));
        }
        return new Pair<OrderPoly<BigIntImmutable>, List<OrderPoly<BigIntImmutable>>>(inter, coeffs);
    }

    /**
     * Computes monotonicity requirements for symbols in rules marked as strict
     */
    private static void computeMonotonicityRequirements1(
            final State st,
            final Set<OrderPolyConstraint<BigIntImmutable>> constraints) {
        for (final Map.Entry<Rule, OrderPoly<BigIntImmutable>> e : st.ruleIsStrictVars.entrySet()) {
            final Rule rule = e.getKey();
            final OrderPoly<BigIntImmutable> ruleIsStrictVar = st.ruleIsStrictVars.get(rule);
            final Map<FunctionSymbol, BitSet> monotone =
                new LinkedHashMap<FunctionSymbol, BitSet>();
            CpxTrsDirectGcdpComplexityProcessor.monotonicityConstraintsForRule(monotone, rule.getRight(), st.definedSyms);
            for (final Map.Entry<FunctionSymbol, BitSet> monEntry : monotone.entrySet()) {
                final BitSet monPos = monEntry.getValue();
                for (int i=monPos.nextSetBit(0); i>=0; i=monPos.nextSetBit(i+1)) {
                    final OrderPoly<BigIntImmutable> monPosVar =
                        st.monotonicityConstraintVars.get(monEntry.getKey()).get(i);
                    constraints.add(st.cs.geConstraint(monPosVar, ruleIsStrictVar));
                }
            }
        }
    }

    /**
     * Compute monotonicity requirements for symbols above positions where
     * the solver decided pairPosVar == 0.
     */
    private static void computeMonotonicityRequirements2(
            final DefinedPositionsTree dpt, final State st,
            final Set<OrderPolyConstraint<BigIntImmutable>> constraints) {
        if (dpt.t != null) {
            for (final DefinedPositionsTree subt : dpt.sub) {
                final Position diffp = subt.p.tail(dpt.p.getDepth());

                TRSFunctionApplication fa = dpt.t;
                FunctionSymbol rootSym = st.fsToPs.get(fa.getRootSymbol());
                for (final int i : diffp) {

                    /* fa.getRootSymbol() must be strongly monotone at i,
                     * if subt.pairPosVar is 0 */
                    final OrderPoly<BigIntImmutable> monPosVar =
                        st.monotonicityConstraintVars.get(rootSym).get(i);
                    final OrderPoly<BigIntImmutable> oneMinusPpv =
                        st.cs.orderPolyFactory.minus(
                                st.cs.orderPolyFactory.getOne(),
                                subt.pairPosVar);
                    constraints.add(st.cs.geConstraint(monPosVar, oneMinusPpv));

                    fa = (TRSFunctionApplication) fa.getArgument(i);
                    rootSym = fa.getRootSymbol();
                }
            }
        }

        for (final DefinedPositionsTree subt : dpt.sub) {
            CpxTrsDirectGcdpComplexityProcessor.computeMonotonicityRequirements2(subt, st, constraints);
        }
    }

    /**
     * Computes which arguments of function symbols need to be monotone, if t is
     * the right hand side of a rule which is to be oriented strictly.
     */
    private static boolean monotonicityConstraintsForRule(final Map<FunctionSymbol, BitSet> monotone, final TRSTerm t, final Set<FunctionSymbol> defined) {
        if (t.isVariable()) {
            return false;
        }
        final TRSFunctionApplication fa = (TRSFunctionApplication)t;
        final FunctionSymbol rootSym = fa.getRootSymbol();
        boolean hasDefinedChild = false;
        for (int i = 0; i < fa.getArguments().size(); i++) {
            final boolean childHasDefinedChild =
                CpxTrsDirectGcdpComplexityProcessor.monotonicityConstraintsForRule(monotone, fa.getArgument(i), defined);
            hasDefinedChild |= childHasDefinedChild;
            if (childHasDefinedChild) {
                BitSet monPos = monotone.get(rootSym);
                if (monPos == null) {
                    monPos = new BitSet(rootSym.getArity());
                    monotone.put(rootSym, monPos);
                }
                monPos.set(i);
            }
        }
        return hasDefinedChild || defined.contains(rootSym);
    }

    private static FunctionSymbol freshFunctionSymbol(final FreshNameGenerator fng, final String name, final int arity) {
        return FunctionSymbol.create(fng.getFreshName(name, false), arity);
    }

    private static class State {
        public final ImmutableSet<FunctionSymbol> definedSyms;
        public final ImmutableRuleSet<Rule> rules;
        public final ImmutableSet<FunctionSymbol> signature;
        public final ConstraintStuff cs;

        public Set<Rule> usableRules;
        public Set<Rule> pairs;
        public AdditionalRestrictions additionalRestrictions;
        public Map<Rule, OrderPoly<BigIntImmutable>> ruleIsStrictVars;

        /**
         * Maps function symbols to pair symbols
         *  */
        public Map<FunctionSymbol,FunctionSymbol> fsToPs =
            new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        public Map<FunctionSymbol,FunctionSymbol> psToFs =
            new LinkedHashMap<FunctionSymbol, FunctionSymbol>();

        public FreshNameGenerator fng;

        public State(final RuntimeComplexityTrsProblem cpx, final ConstraintStuff cs) {
            this.cs = cs;

            this.rules = new ImmutableRuleSet<Rule>(cpx.getR());
            this.definedSyms = cpx.getDefinedSymbols();
            this.signature = ImmutableCreator.create(
                    aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(this.rules));

            this.fng = new FreshNameGenerator(this.signature, FreshNameGenerator.APPEND_NUMBERS);
        }

        /**
         * Contains for each (function symbol,argument index) pair the variable
         * which signals that the position has to be strongly monotonic.
         *
         * If the variable has value one, the position must be monotonic.
         */
        public final Map<FunctionSymbol, List<OrderPoly<BigIntImmutable>>> monotonicityConstraintVars =
            new LinkedHashMap<FunctionSymbol, List<OrderPoly<BigIntImmutable>>>();

        public final void addMappingFsToPs(final FunctionSymbol fs, final FunctionSymbol ps) {
            this.fsToPs.put(fs, ps);
            this.psToFs.put(ps, fs);
        }
    }

    public static class QtrsDirectGcdpComplexityProof extends CpxProof {

        private final Order<TRSTerm> order;
        private final State st;

        public QtrsDirectGcdpComplexityProof(final Order<TRSTerm> order, final State st) {
            this.order = order;
            this.st = st;
        }
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            // FIXME real proof
            final StringBuilder sb = new StringBuilder();
            sb.append("(Usable) Rules:");
                sb.append(o.set(this.st.usableRules, Export_Util.RULES));
            sb.append("Pairs:");
            sb.append(o.set(this.st.pairs, Export_Util.RULES));
            sb.append(o.export(this.order));
            return sb.toString();
        }

    }

    public static enum AdditionalRestrictions {
        None, LikeWdp, LikeCdp, EachPairLikeWdpOrCdp
    }
    public static class Arguments {
        public int range;
        public OPCSolver<BigIntImmutable> opcSolver;
        public int degree;
        public AdditionalRestrictions additionalRestrictions;
    }
}
