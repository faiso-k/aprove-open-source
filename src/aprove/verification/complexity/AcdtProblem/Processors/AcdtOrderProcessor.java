package aprove.verification.complexity.AcdtProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.AcdtProblem.Utils.TupleDefinedPositions.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
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
 * Computes an upper bound for the complexity of an {@link AcdtProblem}
 * using the generalized Cdp method.
 *
 * XXX: Documentation.
 */
public class AcdtOrderProcessor extends AcdtProblemProcessor {

    private final AdditionalRestrictions additionalRestrictions;
    private final int degree;
    private final OPCSolver<BigIntImmutable> opcSolver;
    private final int range;

    @ParamsViaArgumentObject
    public AcdtOrderProcessor(Arguments arguments) {
        this.degree = arguments.degree;
        this.opcSolver = arguments.opcSolver;
        this.range = arguments.range;
        this.additionalRestrictions = arguments.additionalRestrictions;
    }

    @Override
    protected boolean isCdtApplicable(AcdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(AcdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {

        State st = new State(cdtProblem,
                new ConstraintStuff(this.range, this.opcSolver, Collections.<Citation>emptyList()));
        st.additionalRestrictions = this.additionalRestrictions;

        GPOLO<BigIntImmutable> order =
            AcdtOrderProcessor.findOrdering(cdtProblem, st, this.degree, aborter);

        if (order != null && Globals.DEBUG_NOSCHINSKI) {
            GInterpretation<BigIntImmutable> interp = order.getInterpretation();
            System.err.println("---- RULE INTERP ----");
            for (Rule r : st.rules) {
                System.err.println(r + ": " + AcdtOrderProcessor.niceInterpretRule(st.cs, interp, r, aborter));
            }
            System.err.println("---- TUPLE INTERP ----");
            for (Rule r : st.tupleRules) {
                System.err.println(r + ": " + AcdtOrderProcessor.niceInterpretRule(st.cs, interp, r, aborter));
            }
        }

        if (Globals.useAssertions && order != null) {
            GInterpretation<BigIntImmutable> interp = order.getInterpretation();
            SanityChecks.flatten(interp);
            LinkedHashSet<FunctionSymbol> nonConstructors =
                new LinkedHashSet<FunctionSymbol>(cdtProblem.getDefinedPSymbols());
            nonConstructors.addAll(cdtProblem.getDefinedRSymbols());
            assert(SanityChecks.constructorSymbolsStronglyLinear(
                    interp, nonConstructors, true));

            LinkedHashMap<FunctionSymbol, BitSet> monotonicityRequirements =
                new LinkedHashMap<FunctionSymbol, BitSet>();
            for (Map.Entry<FunctionSymbol, List<OrderPoly<BigIntImmutable>>> mcv
                    : st.monotonicityConstraintVars.entrySet()) {
                FunctionSymbol fs = mcv.getKey();
                BitSet monArgs = new BitSet(fs .getArity());

                int i = 0;
                for (OrderPoly<BigIntImmutable> monPoly : mcv.getValue()) {
                    /* monPoly just wraps a GPolyVar */
                    GPolyVar var =  monPoly.getInnerVariables().iterator().next();
                    BigIntImmutable val = st.cs.solution.get(var);
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
                    ComplexityYNM.createUpper(ComplexityValue.fixedDegreePoly(Math.abs(degree))),
                    new QtrsDirectGcdpComplexityProof(order, st));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private static GPOLO<BigIntImmutable> findOrdering(AcdtProblem cdtProblem,
            State st, int degree,Abortion aborter)
            throws AbortionException {
        GInterpretation<BigIntImmutable> interp = st.cs.gInterpretation;

        Set<OrderPolyConstraint<BigIntImmutable>> constraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();

        ImmutableSet<Acdt> tuples = cdtProblem.getTuples();
        st.tupleRules = new LinkedHashSet<Rule>(tuples.size());
        for (Acdt cdt : tuples) {
            st.tupleRules.add(cdt.getRule());
        }

        Map<Acdt, ArrayList<OrderPoly<BigIntImmutable>>> cdt2compoundCoeffs =
            new LinkedHashMap<Acdt, ArrayList<OrderPoly<BigIntImmutable>>>(st.rules.size());
        /* Add constraints for pair rules*/
        for (Acdt cdt : cdtProblem.getTuples()) {

            FunctionSymbol compound = cdt.getCompoundSym();
            Pair<OrderPoly<BigIntImmutable>, ArrayList<OrderPoly<BigIntImmutable>>> compoundInterp =
                AcdtOrderProcessor.interpretCompoundSymbol(st.cs, compound);
            interp.extend(compound,
                    compoundInterp.x, aborter);
            cdt2compoundCoeffs.put(cdt, compoundInterp.y);
        }

        QTRSProblem qtrs = QTRSProblem.create(cdtProblem.getR()).createInnermost();
        QUsableRules quc = new QUsableRules(qtrs);
        st.usableRules = new ImmutableRuleSet<Rule>(quc.getUsableRules(st.tupleRules));

        {
            GInterpretationMode<BigIntImmutable> form =
                new GInterpretationModeDegree<BigIntImmutable>(degree);
            AcdtOrderProcessor.interpretFunctionSymbols(st, form, cdtProblem, aborter);
        }

        {
            Set<OrderPolyConstraint<BigIntImmutable>> tupleConstraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>(st.tupleRules.size());
            for (Rule pair : st.tupleRules) {
                tupleConstraints.add(interp.getPolynomialConstraint(pair, ConstraintType.GT,
                        aborter));
            }
            constraints.add(st.cs.commentedAnd("Pairs", tupleConstraints));
        }

        {
            Set<OrderPolyConstraint<BigIntImmutable>> compoundCoeffsConstraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>(st.tupleRules.size());
            for (Acdt cdt : cdtProblem.getTuples()) {
                ArrayList<Integer> dependencies = cdt.getTupleDefPos().getDependencies();
                List<OrderPoly<BigIntImmutable>> compoundCoeffs =
                    cdt2compoundCoeffs.get(cdt);
                compoundCoeffsConstraints.add(
                        AcdtOrderProcessor.computeConstraintsOnRelPosVars(st, dependencies, compoundCoeffs));
            }
            constraints.add(st.cs.commentedAnd("Constraints on compound coefficients", compoundCoeffsConstraints));
        }

        st.ruleIsStrictVars =
            new LinkedHashMap<Rule, OrderPoly<BigIntImmutable>>(st.usableRules.size());
        for (Rule rule : st.usableRules) {
            GPolyVar coeffVar = st.cs.gInterpretation.getNextCoeff(
                        "str_" , st.cs.boolRange);
            st.ruleIsStrictVars.put(rule, st.cs.makeOrderPolyFromVar(coeffVar));
        }

        /* Add strong monotonicity constraints */
        {
            Set<OrderPolyConstraint<BigIntImmutable>> monotonicityConstraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
            for(FunctionSymbol fs : cdtProblem.getSignature()) {
                if (interp.getPol().get(fs) == null) {
                    continue;
                }
                List<OrderPoly<BigIntImmutable>> monConstVars =
                    BigIntImmutableRing.getStrongMonotonicityConstraints(
                            interp, fs, monotonicityConstraints, st.cs.boolRange);
                st.monotonicityConstraintVars.put(fs, monConstVars);
            }
            constraints.add(st.cs.commentedAnd(
                    "Monotonicity Constraints", monotonicityConstraints));
        }

        /* Compute strong monotonicity requirements */
        {
            Set<OrderPolyConstraint<BigIntImmutable>> monReq1Constraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
            Set<OrderPolyConstraint<BigIntImmutable>> monReq2Constraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
            AcdtOrderProcessor.computeMonotonicityRequirements1(st, monReq1Constraints);
            for (Acdt cdt : cdtProblem.getTuples()) {
                ArrayList<OrderPoly<BigIntImmutable>> rpv = cdt2compoundCoeffs.get(cdt);
                AcdtOrderProcessor.computeMonotonicityRequirements2(cdt, rpv, st, monReq2Constraints);
            }
            constraints.add(st.cs.commentedAnd(
                    "Monotonicity Requirements 1", monReq1Constraints));
            constraints.add(st.cs.commentedAnd(
                    "Monotonicity Requirements 2", monReq2Constraints));
        }


        /* Add usable rules constraints */
        Map<QActiveCondition, GPolyVar> qacCache =
            new LinkedHashMap<QActiveCondition, GPolyVar>();
        Set<Rule> pairsAndRules = new LinkedHashSet<Rule>(st.usableRules);
        pairsAndRules.addAll(st.tupleRules);
        Map<Rule, QActiveCondition> qacMap = quc.getActiveConditions(pairsAndRules);

        Map<Rule, OrderPoly<BigIntImmutable>> qacVarMap =
            new LinkedHashMap<Rule, OrderPoly<BigIntImmutable>>(qacMap.size());

        {
            Set<OrderPolyConstraint<BigIntImmutable>> activeConstraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();

            for (Map.Entry<Rule, QActiveCondition> e : qacMap.entrySet()) {
                Set<OrderPolyConstraint<BigIntImmutable>> ruleActiveConstraints =
                    new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
                GPoly<BigIntImmutable, GPolyVar> activeConditionVar =
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
        Set<OrderPolyConstraint<BigIntImmutable>> oneMinusCompCoeff =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>(st.rules.size());
        Set<OrderPolyConstraint<BigIntImmutable>> activeUsableRulesConstraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        Set<OrderPolyConstraint<BigIntImmutable>> usableRulesConstraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        Set<OrderPolyConstraint<BigIntImmutable>> usableRulesStrictnessConstraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        for (Acdt cdt : cdtProblem.getTuples()) {
            List<OrderPoly<BigIntImmutable>>compoundCoeffs =
                cdt2compoundCoeffs.get(cdt);
            TRSFunctionApplication pairLhs = cdt.getRuleLHS();
            TupleDefinedPositions tupleDefPos = cdt.getTupleDefPos();
            for (int i=0; i < cdt.getRuleRHSArgs().size(); i++) {
                OrderPoly<BigIntImmutable> compoundCoeff =
                    compoundCoeffs.get(i);

                if ((!tupleDefPos.hasAncestor(i))) {
                    Set<Rule> usableRules = quc.getUsableRules(
                            Rule.create(pairLhs, cdt.getRuleRHSArgs().get(i)));

                    for (Rule usableRule : usableRules) {
                        OrderPolyConstraint<BigIntImmutable> constraint =
                            st.cs.condGeConstraint(
                                    st.cs.orderPolyFactory.times(
                                            qacVarMap.get(usableRule),
                                            compoundCoeff),
                                    interp.interpretTerm(usableRule.getLeft(), aborter),
                                    st.cs.orderPolyFactory.plus(
                                            st.ruleIsStrictVars.get(usableRule),
                                            interp.interpretTerm(usableRule.getRight(), aborter))
                                    );
                        constraint = st.cs.constraintFactory.createComment(usableRule.toString(), constraint);
                       activeUsableRulesConstraints.add(constraint);
                    }
                } else {
                    int parentIdx = tupleDefPos.getDependency(i);
                    Position cdtPos = tupleDefPos.getPosition(i);
                    Position parentPos = tupleDefPos.getPosition(parentIdx);
                    TRSFunctionApplication parentRhsArg =
                        cdt.getRuleRHSArgs().get(parentIdx);
                    Position posInParent =
                        cdtPos.tail(parentPos.getDepth());
                    TRSTerm rhs = parentRhsArg.getSubterm(posInParent);
                    Set<Rule> usableRules = quc.getUsableRules(
                            Rule.create(pairLhs, rhs));

                    /* No pair is used for this position */
                    // XXX: move monotonicity constraints here
                    /* oneMinusCc == 1 - compoundCoeff */
                    OrderPoly<BigIntImmutable> oneMinusCc =
                        st.cs.makeOrderPolyFromVar(interp.getNextCoeff(
                                "omr", st.cs.boolRange));
                    oneMinusCompCoeff.add(
                            st.cs.eqConstraint(
                                    st.cs.orderPolyFactory.minus(
                                            st.cs.orderPolyFactory.getOne(),
                                            oneMinusCc),
                                            compoundCoeff)
                    );

                    for (Rule usableRule : usableRules) {
                        usableRulesStrictnessConstraints.add(
                                st.cs.geConstraint(
                                        st.ruleIsStrictVars.get(usableRule),
                                        oneMinusCc)
                        );
                    }
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
                        "One-Minus-CompoundCoeff variables",
                        oneMinusCompCoeff));

        /* Solve constraint */
        OrderPolyConstraint<BigIntImmutable> constraint =
            st.cs.constraintFactory.createAnd(constraints);
        constraint = st.cs.constraintFactory.createQuantifierE(
                constraint, constraint.getFreeVariables());

        if ( Globals.DEBUG_NOSCHINSKI) {
            OPCExportVisitor<BigIntImmutable> export = new OPCExportVisitor<BigIntImmutable>(st.cs.fvInner, st.cs.fvOuter, new PLAIN_Util());
            export.applyTo(constraint);
            System.err.println(new PLAIN_Util().set(st.rules, Export_Util.RULES));
            System.err.println(new PLAIN_Util().set(st.tupleRules, Export_Util.RULES));
            System.err.println(st.ruleIsStrictVars);
            System.err.println(interp);
            System.err.println(export);
        }
        return st.cs.solveConstraint(constraint, aborter);
    }

    private static String niceInterpretRule(ConstraintStuff cs, GInterpretation<BigIntImmutable> interp, Rule r,
            Abortion aborter) throws AbortionException {
        PLAIN_Util eu = new PLAIN_Util();
        OrderPoly<BigIntImmutable> lhsI = interp.interpretTerm(r.getLeft(), aborter);
        OrderPoly<BigIntImmutable> rhsI = interp.interpretTerm(r.getRight(), aborter);
        return lhsI.exportFlatDeep(cs.fvInner, cs.fvOuter, eu) +
                " >?> " + rhsI.exportFlatDeep(cs.fvInner, cs.fvOuter, eu);
    }

    /**
     * Restricts the possible values for relPosVars, i.e. for the coefficients
     * in the interpretation of compound symbols.
     */
    private static OrderPolyConstraint<BigIntImmutable> computeConstraintsOnRelPosVars(
            State st, ArrayList<Integer> pairPosVarDependencies,
            List<OrderPoly<BigIntImmutable>> compoundCoeffs) {
        Set<OrderPolyConstraint<BigIntImmutable>> constraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        OrderPoly<BigIntImmutable> wdpOrCdpVar =
            st.cs.orderPolyFactory.buildFromInnerVariable(
                    st.cs.gInterpretation.getNextCoeff("wc", st.cs.boolRange));
        for (int i = 0; i < pairPosVarDependencies.size(); i++) {
            int parentOfI = pairPosVarDependencies.get(i);
            OrderPoly<BigIntImmutable> cc = compoundCoeffs.get(i);
            if (parentOfI == -1) { // topmost position
                // All topmost defined terms have relPosVar = 1
                constraints.add(st.cs.eqConstraint(cc, st.cs.orderPolyFactory.getOne()));
            } else if (st.additionalRestrictions == AdditionalRestrictions.LikeWdp) {
                constraints.add(st.cs.eqConstraint(cc, st.cs.orderPolyFactory.getZero()));
            } else if (st.additionalRestrictions == AdditionalRestrictions.LikeCdp) {
                constraints.add(st.cs.eqConstraint(cc, st.cs.orderPolyFactory.getOne()));
            } else if (st.additionalRestrictions == AdditionalRestrictions.EachPairLikeWdpOrCdp) {
                constraints.add(st.cs.eqConstraint(cc, wdpOrCdpVar));
            } else { // term on position i depends on term on position parentOfI
                // if relPosVar=0 for one position then
                // relPosVar=0 for all positions below.
                OrderPoly<BigIntImmutable> parentVar =
                    compoundCoeffs.get(parentOfI);
                constraints.add(st.cs.geConstraint(parentVar, cc));
            }
        }
        return st.cs.constraintFactory.createAnd(constraints);
    }

    /**
     * Interprets function symbols (and their pair versions). Fills
     * the fsToPs field of st.
     */
    private static void interpretFunctionSymbols(State st,
            GInterpretationMode<BigIntImmutable> form, AcdtProblem cdtProblem,
            Abortion aborter) throws AbortionException {

        GInterpretationMode<BigIntImmutable> constantForm =
            new GInterpretationModeLinear<BigIntImmutable>(st.cs.boolRange, null);

        Set<FunctionSymbol> occuringSyms =
            aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(st.usableRules);
        occuringSyms.addAll(
                aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(st.tupleRules));

        Set<FunctionSymbol> defSyms =
            new LinkedHashSet<FunctionSymbol>(cdtProblem.getDefinedRSymbols());
        defSyms.addAll(cdtProblem.getDefinedPSymbols());
        defSyms.retainAll(occuringSyms);

        for (FunctionSymbol fs : defSyms) {
            st.cs.gInterpretation.extend(fs, form, aborter);
        }

        occuringSyms.removeAll(defSyms);
        for (FunctionSymbol fs : occuringSyms) {
            st.cs.gInterpretation.extend(fs, constantForm, aborter);
        }
    }

    /**
     * @return The interpretation of <code>fs</code> and the list of
     *         coefficients of the arguments.
     */
    private static Pair<OrderPoly<BigIntImmutable>,ArrayList<OrderPoly<BigIntImmutable>>> interpretCompoundSymbol(
            ConstraintStuff cs,
            FunctionSymbol fs) {
        GInterpretation<BigIntImmutable> interp = cs.gInterpretation;
        OrderPoly<BigIntImmutable> inter = cs.orderPolyFactory.getZero();

        int arity = fs.getArity();
        ArrayList<OrderPoly<BigIntImmutable>> coeffs =
            new ArrayList<OrderPoly<BigIntImmutable>>(arity);

        for (int i=0; i < arity; i++) {
            GPolyVar coeffVar =
                interp.getNextCoeff("cp." + fs.getName() +"." + fs.getArity() + "." + i + "_", cs.boolRange);
            OrderPoly<BigIntImmutable> coeff = cs.makeOrderPolyFromVar(coeffVar);
            coeffs.add(coeff);
            OrderPoly<BigIntImmutable> var =
                cs.orderPolyFactory.buildFromVariable(interp.getVariableForFunctionSymbolArgument(i));
            inter = interp.getFactory().plus(inter,
                    interp.getFactory().times(coeff, var));
        }
        return new Pair<OrderPoly<BigIntImmutable>, ArrayList<OrderPoly<BigIntImmutable>>>(inter, coeffs);
    }

    /**
     * Computes monotonicity requirements for symbols in rules marked as strict
     */
    private static void computeMonotonicityRequirements1(
            State st,
            Set<OrderPolyConstraint<BigIntImmutable>> constraints) {
        for (Map.Entry<Rule, OrderPoly<BigIntImmutable>> e : st.ruleIsStrictVars.entrySet()) {
            Rule rule = e.getKey();
            OrderPoly<BigIntImmutable> ruleIsStrictVar = st.ruleIsStrictVars.get(rule);
            Map<FunctionSymbol, BitSet> monotone =
                new LinkedHashMap<FunctionSymbol, BitSet>();
            AcdtOrderProcessor.monotonicityConstraintsForRule(monotone, rule.getRight(), st.definedSyms);
            for (Map.Entry<FunctionSymbol, BitSet> monEntry : monotone.entrySet()) {
                BitSet monPos = monEntry.getValue();
                for (int i=monPos.nextSetBit(0); i>=0; i=monPos.nextSetBit(i+1)) {
                    OrderPoly<BigIntImmutable> monPosVar =
                        st.monotonicityConstraintVars.get(monEntry.getKey()).get(i);
                    constraints.add(st.cs.geConstraint(monPosVar, ruleIsStrictVar));
                }
            }
        }
    }

    /**
     * Compute monotonicity requirements for symbols above positions where
     * the solver decided compoundCoeff == 0.
     */
    private static void computeMonotonicityRequirements2(
            Acdt cdt, ArrayList<OrderPoly<BigIntImmutable>> compoundCoeffs, State st,
            Set<OrderPolyConstraint<BigIntImmutable>> constraints) {
        TupleDefinedPositions tdps = cdt.getTupleDefPos();
        for (TupleDefinedPosition tdp : tdps) {
            OrderPoly<BigIntImmutable> compoundCoeff = compoundCoeffs.get(tdp.idx);
            if (tdps.hasAncestor(tdp.idx)) {
                /* has an ancestor. all positions down to this parent must be strongly monotone */
                final int ancIdx = tdps.getDependency(tdp.idx);
                Position diffp = tdp.position.tail(tdps.getPosition(tdps.getDependency(tdp.idx)).getDepth());
                TRSFunctionApplication fa = cdt.getRuleRHSArgs().get(ancIdx);
                for (int i : diffp) {
                    /* fa.getRootSymbol() must be strongly monotone at i,
                     * if subt.pairPosVar is 0 */
                    OrderPoly<BigIntImmutable> monPosVar =
                        st.monotonicityConstraintVars.get(fa.getRootSymbol()).get(i);
                    OrderPoly<BigIntImmutable> oneMinusCc =
                        st.cs.orderPolyFactory.minus(
                                st.cs.orderPolyFactory.getOne(),
                                compoundCoeff);
                    constraints.add(st.cs.geConstraint(monPosVar, oneMinusCc));

                    fa = (TRSFunctionApplication) fa.getArgument(i);
                }

            }
        }
    }

    /**
     * Computes which arguments of function symbols need to be monotone, if t is
     * the right hand side of a rule which is to be oriented strictly.
     */
    private static boolean monotonicityConstraintsForRule(Map<FunctionSymbol, BitSet> monotone, TRSTerm t, Set<FunctionSymbol> defined) {
        if (t.isVariable()) {
            return false;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication)t;
        FunctionSymbol rootSym = fa.getRootSymbol();
        boolean hasDefinedChild = false;
        for (int i = 0; i < fa.getArguments().size(); i++) {
            boolean childHasDefinedChild =
                AcdtOrderProcessor.monotonicityConstraintsForRule(monotone, fa.getArgument(i), defined);
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

    private static class State {
        public final ImmutableSet<FunctionSymbol> definedSyms;
        public final ImmutableRuleSet<Rule> rules;
        public final ImmutableSet<FunctionSymbol> signature;
        public final ConstraintStuff cs;

        public Set<Rule> usableRules;
        public Set<Rule> tupleRules;
        public AdditionalRestrictions additionalRestrictions;
        public Map<Rule, OrderPoly<BigIntImmutable>> ruleIsStrictVars;

        public State(AcdtProblem cdtProblem, ConstraintStuff cs) {
            this.cs = cs;

            this.rules = new ImmutableRuleSet<Rule>(cdtProblem.getR());
            this.definedSyms = cdtProblem.getDefinedRSymbols();
            this.signature = cdtProblem.getSignature();
            new FreshNameGenerator(this.signature, FreshNameGenerator.APPEND_NUMBERS);
        }

        /**
         * Contains for each (function symbol,argument index) pair the variable
         * which signals that the position has to be strongly monotonic.
         *
         * If the variable has value one, the position must be monotonic.
         */
        public final Map<FunctionSymbol, List<OrderPoly<BigIntImmutable>>> monotonicityConstraintVars =
            new LinkedHashMap<FunctionSymbol, List<OrderPoly<BigIntImmutable>>>();
    }

    public static class QtrsDirectGcdpComplexityProof extends Proof.DefaultProof {

        private final Order<TRSTerm> order;
        private final State st;

        public QtrsDirectGcdpComplexityProof(Order<TRSTerm> order, State st) {
            this.order = order;
            this.st = st;
        }
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME real proof
            StringBuilder sb = new StringBuilder();
            sb.append("(Usable) Rules:");
                sb.append(o.set(this.st.usableRules, Export_Util.RULES));
            sb.append("Pairs:");
            sb.append(o.set(this.st.tupleRules, Export_Util.RULES));
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
