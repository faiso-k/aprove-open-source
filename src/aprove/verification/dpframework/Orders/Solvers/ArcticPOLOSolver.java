package aprove.verification.dpframework.Orders.Solvers;

import java.math.*;
import java.util.*;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.SMTUtility.*;
import immutables.*;

/**
 * Solver for polynomial orderings with arctic numbers.
 * Uses an SMT checker to generate arbitrary numbers.
 *
 * The number format we use here is:
 * <n, b> where n is an integer value and
 * b is a bool value.
 * if b is set the number is -inf
 * it is n if b is not set.
 *
 * @author Andreas Kelle-Emden
 * $Id:$
 */
public class ArcticPOLOSolver implements AbortableConstraintSolver<TRSTerm> {

    private SMTEngine smtChecker = null;

    private static final SMTLIBIntConstant iZero = SMTLIBIntConstant.create(BigInteger.ZERO);
    private static final Pair<SMTLIBIntValue, SMTLIBBoolValue> arcticOne = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(
        ArcticPOLOSolver.iZero, SMTLIBBoolFalse.create());
    private static final Pair<SMTLIBIntValue, SMTLIBBoolValue> arcticZero = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(
        ArcticPOLOSolver.iZero, SMTLIBBoolTrue.create());

    public ArcticPOLOSolver(final SMTEngine smtChecker) {
        this.smtChecker = smtChecker;
    }

    /**
     * Encode arctic multiplication:
     * a*b = -inf iff a = -inf or b = -inf
     * a*b = a+b else
     *
     * @param a first arctic number
     * @param b second arctic number
     * @param res the resulting arctic number
     * @param formFactory
     */
    private Formula<SMTLIBTheoryAtom> encodeAdd(final Pair<SMTLIBIntValue, SMTLIBBoolValue> a,
        final Pair<SMTLIBIntValue, SMTLIBBoolValue> b,
        final Pair<SMTLIBIntValue, SMTLIBBoolValue> res,
        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory) {
        final Formula<SMTLIBTheoryAtom> or =
            formFactory.buildOr(formFactory.buildTheoryAtom(a.y), formFactory.buildTheoryAtom(b.y));
        final List<SMTLIBIntValue> addList = new ArrayList<SMTLIBIntValue>(2);
        addList.add(a.x);
        addList.add(b.x);
        final SMTLIBIntPlus plus = SMTLIBIntPlus.create(addList);
        final SMTLIBIntEquals eq1 = SMTLIBIntEquals.create(res.x, plus);
        final Formula<SMTLIBTheoryAtom> eq2 = formFactory.buildTheoryAtom(res.y);
        return formFactory.buildIte(
            or,
            eq2,
            formFactory.buildAnd(formFactory.buildTheoryAtom(eq1),
                formFactory.buildNot(formFactory.buildTheoryAtom(res.y))));
    }

    /**
     * Encode arctic addition:
     * +{a,b, ...} = -inf iff all numbers are -inf
     * +{a,b, ...} = max{a,b, ...} for all numbers which are not -inf else
     *
     * @param vals arctic number
     * @param res the resulting arctic number
     * @param formFactory
     */
    private Formula<SMTLIBTheoryAtom> encodeMax(final Pair<SMTLIBIntValue, SMTLIBBoolValue> left,
        final Pair<SMTLIBIntValue, SMTLIBBoolValue> right,
        final Pair<SMTLIBIntValue, SMTLIBBoolValue> res,
        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory) {
        final Formula<SMTLIBTheoryAtom> lTrue = formFactory.buildTheoryAtom(left.y);
        final Formula<SMTLIBTheoryAtom> rTrue = formFactory.buildTheoryAtom(right.y);
        final Formula<SMTLIBTheoryAtom> resTrue = formFactory.buildTheoryAtom(res.y);
        final List<Formula<SMTLIBTheoryAtom>> retLList = new ArrayList<Formula<SMTLIBTheoryAtom>>(2);
        retLList.add(formFactory.buildTheoryAtom(SMTLIBIntEquals.create(left.x, res.x)));
        retLList.add(formFactory.buildIff(lTrue, resTrue));
        final Formula<SMTLIBTheoryAtom> retL = formFactory.buildAnd(retLList);
        final List<Formula<SMTLIBTheoryAtom>> retRList = new ArrayList<Formula<SMTLIBTheoryAtom>>(2);
        retRList.add(formFactory.buildTheoryAtom(SMTLIBIntEquals.create(right.x, res.x)));
        retRList.add(formFactory.buildIff(rTrue, resTrue));
        final Formula<SMTLIBTheoryAtom> retR = formFactory.buildAnd(retRList);
        final Formula<SMTLIBTheoryAtom> ge = formFactory.buildTheoryAtom(SMTLIBIntGE.create(left.x, right.x));
        final Formula<SMTLIBTheoryAtom> numberCMP = formFactory.buildIte(ge, retL, retR);
        final Formula<SMTLIBTheoryAtom> rInfinite = formFactory.buildIte(rTrue, retL, numberCMP);
        final Formula<SMTLIBTheoryAtom> lInfinite = formFactory.buildIte(lTrue, retR, rInfinite);
        return lInfinite;
    }

    private Formula<SMTLIBTheoryAtom> encodeMax(final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> vals,
        final Pair<SMTLIBIntValue, SMTLIBBoolValue> res,
        final SMTLIBIntVariableGenerator vgI,
        final SMTLIBBoolVariableGenerator vgB,
        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory) {
        final int size = vals.size();
        if (size == 0) {
            return formFactory.buildTheoryAtom(res.y);
        } else if (size == 1) {
            final Pair<SMTLIBIntValue, SMTLIBBoolValue> val = vals.get(0);
            final List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(2);
            andList.add(formFactory.buildTheoryAtom(SMTLIBIntEquals.create(val.x, res.x)));
            andList.add(formFactory.buildIff(formFactory.buildTheoryAtom(res.y), formFactory.buildTheoryAtom(val.y)));
            return formFactory.buildAnd(andList);
        } else {
            Pair<SMTLIBIntValue, SMTLIBBoolValue> result = vals.get(0);
            final List<Formula<SMTLIBTheoryAtom>> formList = new ArrayList<Formula<SMTLIBTheoryAtom>>(size + 1);
            for (int i = 1; i < size; i++) {
                final Pair<SMTLIBIntValue, SMTLIBBoolValue> left = vals.get(i);
                final Pair<SMTLIBIntValue, SMTLIBBoolValue> newRes =
                    new Pair<SMTLIBIntValue, SMTLIBBoolValue>(vgI.getNewVariable(), vgB.getNewVariable());
                formList.add(this.encodeMax(left, result, newRes, formFactory));
                result = newRes;
            }
            formList.add(formFactory.buildTheoryAtom(SMTLIBIntEquals.create(result.x, res.x)));
            formList.add(formFactory.buildIff(formFactory.buildTheoryAtom(res.y), formFactory.buildTheoryAtom(result.y)));
            return formFactory.buildAnd(formList);
        }
    }

    private void buildVarToValMap(final TRSTerm t,
        final Map<FunctionSymbol, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> symToParamsMap,
        final Map<FunctionSymbol, Pair<SMTLIBIntValue, SMTLIBBoolValue>> symToConsMap,
        final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMap,
        final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantVals,
        final Pair<SMTLIBIntValue, SMTLIBBoolValue> param,
        final SMTLIBIntVariableGenerator vgI,
        final SMTLIBBoolVariableGenerator vgB,
        final List<Formula<SMTLIBTheoryAtom>> formList,
        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory) {

        if (t.isVariable()) {
            final TRSVariable vt = (TRSVariable) t;
            List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> values = varToValMap.get(vt);
            if (values == null) {
                values = new LinkedList<Pair<SMTLIBIntValue, SMTLIBBoolValue>>();
                varToValMap.put(vt, values);
            }

            values.add(param);

        } else {
            final TRSFunctionApplication fat = (TRSFunctionApplication) t;
            final FunctionSymbol symt = fat.getRootSymbol();
            final Pair<SMTLIBIntValue, SMTLIBBoolValue> cons = symToConsMap.get(symt);
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> params = symToParamsMap.get(symt);
            // Collect constant value
            SMTLIBIntVariable iNew = vgI.getNewVariable();
            SMTLIBBoolVariable bNew = vgB.getNewVariable();
            Pair<SMTLIBIntValue, SMTLIBBoolValue> newVal = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(iNew, bNew);
            formList.add(this.encodeAdd(cons, param, newVal, formFactory));
            constantVals.add(newVal);
            // Collect values for the parameters
            int i = 0;
            for (final Pair<SMTLIBIntValue, SMTLIBBoolValue> p : params) {
                iNew = vgI.getNewVariable();
                bNew = vgB.getNewVariable();
                newVal = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(iNew, bNew);
                formList.add(this.encodeAdd(p, param, newVal, formFactory));

                this.buildVarToValMap(fat.getArgument(i), symToParamsMap, symToConsMap, varToValMap, constantVals, newVal,
                    vgI, vgB, formList, formFactory);
                i++;
            }
        }
    }

    // Encode greater-equal on numbers, where
    // a >= b iff either
    // b = -inf or
    // b != -inf, a != -inf and a >= b in natural numbers
    private Formula<SMTLIBTheoryAtom> encodeNumberGE(final Pair<SMTLIBIntValue, SMTLIBBoolValue> a,
        final Pair<SMTLIBIntValue, SMTLIBBoolValue> b,
        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory) {
        final SMTLIBIntGE ge = SMTLIBIntGE.create(a.x, b.x);
        final Formula<SMTLIBTheoryAtom> notA = formFactory.buildNot(formFactory.buildTheoryAtom(a.y));
        final Formula<SMTLIBTheoryAtom> and = formFactory.buildAnd(notA, formFactory.buildTheoryAtom(ge));
        return formFactory.buildOr(and, formFactory.buildTheoryAtom(b.y));
    }

    // Encode greater-then on numbers, where
    // a > b iff either
    // b = -inf or
    // b != -inf, a != -inf and a > b in natural numbers
    private Formula<SMTLIBTheoryAtom> encodeNumberGT(final Pair<SMTLIBIntValue, SMTLIBBoolValue> a,
        final Pair<SMTLIBIntValue, SMTLIBBoolValue> b,
        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory) {
        final SMTLIBIntGT gt = SMTLIBIntGT.create(a.x, b.x);
        final Formula<SMTLIBTheoryAtom> notA = formFactory.buildNot(formFactory.buildTheoryAtom(a.y));
        final Formula<SMTLIBTheoryAtom> and = formFactory.buildAnd(notA, formFactory.buildTheoryAtom(gt));
        return formFactory.buildOr(and, formFactory.buildTheoryAtom(b.y));
    }

    // Encode GREATER EQUAL
    private Formula<SMTLIBTheoryAtom> addGE(final SMTLIBBoolVariable var,
        final Set<TRSVariable> varSet,
        final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMapL,
        final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantValsL,
        final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMapR,
        final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantValsR,
        final SMTLIBIntVariableGenerator vgI,
        final SMTLIBBoolVariableGenerator vgB,
        final List<Formula<SMTLIBTheoryAtom>> formList,
        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory) {
        final List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(varSet.size() + 1);
        // Compare constant values
        Pair<SMTLIBIntValue, SMTLIBBoolValue> consL;
        if (constantValsL.isEmpty()) {
            consL = ArcticPOLOSolver.arcticZero;
        } else {
            consL = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(vgI.getNewVariable(), vgB.getNewVariable());
            formList.add(this.encodeMax(constantValsL, consL, vgI, vgB, formFactory));
        }
        Pair<SMTLIBIntValue, SMTLIBBoolValue> consR;
        if (constantValsR.isEmpty()) {
            consR = ArcticPOLOSolver.arcticZero;
        } else {
            consR = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(vgI.getNewVariable(), vgB.getNewVariable());
            formList.add(this.encodeMax(constantValsR, consR, vgI, vgB, formFactory));
        }

        andList.add(this.encodeNumberGE(consL, consR, formFactory));

        // Compare variables
        for (final TRSVariable v : varSet) {
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> valsL = varToValMapL.get(v);
            Pair<SMTLIBIntValue, SMTLIBBoolValue> varL;
            if (valsL == null || valsL.isEmpty()) {
                varL = ArcticPOLOSolver.arcticZero;
            } else {
                varL = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(vgI.getNewVariable(), vgB.getNewVariable());
                formList.add(this.encodeMax(valsL, varL, vgI, vgB, formFactory));
            }
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> valsR = varToValMapR.get(v);
            Pair<SMTLIBIntValue, SMTLIBBoolValue> varR;
            if (valsR == null || valsR.isEmpty()) {
                varR = ArcticPOLOSolver.arcticZero;
            } else {
                varR = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(vgI.getNewVariable(), vgB.getNewVariable());
                formList.add(this.encodeMax(valsR, varR, vgI, vgB, formFactory));
            }

            andList.add(this.encodeNumberGE(varL, varR, formFactory));
        }
        return formFactory.buildIff(formFactory.buildTheoryAtom(var), formFactory.buildAnd(andList));
    }

    // Encode GREATER THEN
    private Formula<SMTLIBTheoryAtom> addGT(final SMTLIBBoolVariable var,
        final Set<TRSVariable> varSet,
        final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMapL,
        final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantValsL,
        final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMapR,
        final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantValsR,
        final SMTLIBIntVariableGenerator vgI,
        final SMTLIBBoolVariableGenerator vgB,
        final List<Formula<SMTLIBTheoryAtom>> formList,
        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory) {
        final List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(varSet.size() + 1);
        // Compare constant values
        Pair<SMTLIBIntValue, SMTLIBBoolValue> consL;
        if (constantValsL.isEmpty()) {
            consL = ArcticPOLOSolver.arcticZero;
        } else {
            consL = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(vgI.getNewVariable(), vgB.getNewVariable());
            formList.add(this.encodeMax(constantValsL, consL, vgI, vgB, formFactory));
        }
        Pair<SMTLIBIntValue, SMTLIBBoolValue> consR;
        if (constantValsR.isEmpty()) {
            consR = ArcticPOLOSolver.arcticZero;
        } else {
            consR = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(vgI.getNewVariable(), vgB.getNewVariable());
            formList.add(this.encodeMax(constantValsR, consR, vgI, vgB, formFactory));
        }

        andList.add(this.encodeNumberGT(consL, consR, formFactory));

        // Compare variables
        for (final TRSVariable v : varSet) {
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> valsL = varToValMapL.get(v);
            Pair<SMTLIBIntValue, SMTLIBBoolValue> varL;
            if (valsL == null || valsL.isEmpty()) {
                varL = ArcticPOLOSolver.arcticZero;
            } else {
                varL = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(vgI.getNewVariable(), vgB.getNewVariable());
                formList.add(this.encodeMax(valsL, varL, vgI, vgB, formFactory));
            }
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> valsR = varToValMapR.get(v);
            Pair<SMTLIBIntValue, SMTLIBBoolValue> varR;
            if (valsR == null || valsR.isEmpty()) {
                varR = ArcticPOLOSolver.arcticZero;
            } else {
                varR = new Pair<SMTLIBIntValue, SMTLIBBoolValue>(vgI.getNewVariable(), vgB.getNewVariable());
                formList.add(this.encodeMax(valsR, varR, vgI, vgB, formFactory));
            }

            andList.add(this.encodeNumberGT(varL, varR, formFactory));
        }
        return formFactory.buildIff(formFactory.buildTheoryAtom(var), formFactory.buildAnd(andList));
    }

    // Solve constraints only
    @Override
    public final ExportableOrder<TRSTerm> solve(final Collection<Constraint<TRSTerm>> constraints, final Abortion aborter)
            throws AbortionException {
        return this.solve(constraints, null, aborter);
    }

    // Solve constraints and non-strict rules
    public ArcticPOLO solve(final Collection<Constraint<TRSTerm>> cons, final Set<Rule> nonStrict, final Abortion aborter)
            throws AbortionException {
        return this.solve(null, cons, nonStrict, null, aborter);
    }

    // Solve constraints and non-strict rules w.r.t. mu
    public ArcticPOLO solve(final Collection<Constraint<TRSTerm>> cons,
        final Set<Rule> nonStrict,
        final ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu,
        final Abortion aborter) throws AbortionException {
        return this.solve(null, cons, nonStrict, mu, aborter);
    }

    // Solve constraints and non-strict rules w.r.t. mu and Q active conditions
    public ArcticPOLO solve(Map<? extends GeneralizedRule, QActiveCondition> R,
        Collection<Constraint<TRSTerm>> cons,
        Set<? extends GeneralizedRule> nonStrict,
        final ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu,
        final Abortion aborter) throws AbortionException {
        final FullSharingFlatteningFactory<SMTLIBTheoryAtom> formFactory =
            new FullSharingFlatteningFactory<SMTLIBTheoryAtom>();

        if (cons == null) {
            cons = new LinkedHashSet<Constraint<TRSTerm>>();
        }
        if (nonStrict == null) {
            nonStrict = new LinkedHashSet<GeneralizedRule>();
        }
        if (R == null) {
            R = new LinkedHashMap<Rule, QActiveCondition>();
        }
        final Collection<Constraint<TRSTerm>> cs = new LinkedHashSet<Constraint<TRSTerm>>(cons);

        for (final GeneralizedRule rule : nonStrict) {
            cs.add(Constraint.fromRule(rule, OrderRelation.GE));
        }
        for (final Map.Entry<? extends GeneralizedRule, QActiveCondition> e : R.entrySet()) {
            cs.add(Constraint.fromRule(e.getKey(), OrderRelation.GE));
        }

        // Create variable maps
        final Set<FunctionSymbol> symSet = Constraint.getFunctionSymbols(cs);
        final Map<FunctionSymbol, Pair<SMTLIBIntValue, SMTLIBBoolValue>> funToConsMap =
            new LinkedHashMap<FunctionSymbol, Pair<SMTLIBIntValue, SMTLIBBoolValue>>();
        final Map<FunctionSymbol, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> funToVarsMap =
            new LinkedHashMap<FunctionSymbol, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>>();

        for (final FunctionSymbol sym : symSet) {
            final int arity = sym.getArity();
            final String symName = sym.getName();
            // Define variable for constant value
            final SMTLIBIntVariable vi = SMTLIBIntVariable.create("icons_" + arity + "_" + symName);
            final SMTLIBBoolVariable vb = SMTLIBBoolVariable.create("bcons_" + arity + "_" + symName);
            funToConsMap.put(sym, new Pair<SMTLIBIntValue, SMTLIBBoolValue>(vi, vb));
            // Define variables for parameters
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> paramList =
                new ArrayList<Pair<SMTLIBIntValue, SMTLIBBoolValue>>(arity);
            for (int i = 0; i < arity; i++) {
                final SMTLIBIntVariable pi = SMTLIBIntVariable.create("iparam_" + arity + "_" + symName + "_" + i);
                final SMTLIBBoolVariable pb = SMTLIBBoolVariable.create("bparam_" + arity + "_" + symName + "_" + i);
                paramList.add(new Pair<SMTLIBIntValue, SMTLIBBoolValue>(pi, pb));
            }
            funToVarsMap.put(sym, paramList);
        }
        final Set<TRSVariable> varSet = Constraint.getVariables(cs);

        aborter.checkAbortion();

        // Encode general constraints
        final List<Formula<SMTLIBTheoryAtom>> formList = new LinkedList<Formula<SMTLIBTheoryAtom>>();
        for (final FunctionSymbol sym : symSet) {
            final int arity = sym.getArity();
            final List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(arity + 2);
            final Pair<SMTLIBIntValue, SMTLIBBoolValue> val = funToConsMap.get(sym);
            // Constant part must be >= 0
            andList.add(formFactory.buildNot(formFactory.buildTheoryAtom(val.y)));
            andList.add(formFactory.buildTheoryAtom(SMTLIBIntGE.create(val.x, ArcticPOLOSolver.iZero)));
            formList.add(formFactory.buildAnd(andList));
        }

        final SMTLIBIntVariableGenerator vgI = SMTLIBIntVariableGenerator.create("int");
        final SMTLIBBoolVariableGenerator vgB = SMTLIBBoolVariableGenerator.create("bool");

        final List<Formula<SMTLIBTheoryAtom>> nonStrictGTs = new ArrayList<Formula<SMTLIBTheoryAtom>>(nonStrict.size());
        // Encode linear poly constraints
        int count = 0;
        for (final GeneralizedRule rule : nonStrict) {
            aborter.checkAbortion();
            count++;
            final TRSTerm l = rule.getLeft();
            final TRSTerm r = rule.getRight();
            // Collect values for l
            final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMapL =
                new LinkedHashMap<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>>();
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantValsL =
                new LinkedList<Pair<SMTLIBIntValue, SMTLIBBoolValue>>();
            this.buildVarToValMap(l, funToVarsMap, funToConsMap, varToValMapL, constantValsL, ArcticPOLOSolver.arcticOne, vgI, vgB, formList,
                formFactory);
            // Collect values for r
            final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMapR =
                new LinkedHashMap<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>>();
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantValsR =
                new LinkedList<Pair<SMTLIBIntValue, SMTLIBBoolValue>>();
            this.buildVarToValMap(r, funToVarsMap, funToConsMap, varToValMapR, constantValsR, ArcticPOLOSolver.arcticOne, vgI, vgB, formList,
                formFactory);

            // Encode and define gr and ge constraint
            final SMTLIBBoolVariable gt = SMTLIBBoolVariable.create("gt" + count);
            formList.add(this.addGT(gt, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, vgI, vgB,
                formList, formFactory));
            nonStrictGTs.add(formFactory.buildTheoryAtom(gt));
            final SMTLIBBoolVariable ge = SMTLIBBoolVariable.create("ge" + count);
            formList.add(this.addGE(ge, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, vgI, vgB,
                formList, formFactory));
            formList.add(formFactory.buildTheoryAtom(ge));
        }
        for (final Map.Entry<? extends GeneralizedRule, QActiveCondition> e : R.entrySet()) {
            count++;
            final GeneralizedRule rule = e.getKey();
            final TRSTerm l = rule.getLeft();
            final TRSTerm r = rule.getRight();
            // Collect values for l
            final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMapL =
                new LinkedHashMap<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>>();
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantValsL =
                new LinkedList<Pair<SMTLIBIntValue, SMTLIBBoolValue>>();
            this.buildVarToValMap(l, funToVarsMap, funToConsMap, varToValMapL, constantValsL, ArcticPOLOSolver.arcticOne, vgI, vgB, formList,
                formFactory);
            // Collect values for r
            final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMapR =
                new LinkedHashMap<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>>();
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantValsR =
                new LinkedList<Pair<SMTLIBIntValue, SMTLIBBoolValue>>();
            this.buildVarToValMap(r, funToVarsMap, funToConsMap, varToValMapR, constantValsR, ArcticPOLOSolver.arcticOne, vgI, vgB, formList,
                formFactory);

            // Encode and define ge constraint
            final SMTLIBBoolVariable ge = SMTLIBBoolVariable.create("ge" + count);
            formList.add(this.addGE(ge, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, vgI, vgB,
                formList, formFactory));

            // Encode Q active constraint
            final QActiveCondition qac = e.getValue();
            final Set<? extends Set<Pair<FunctionSymbol, Integer>>> setRepresentation = qac.getSetRepresentation();

            final List<Formula<SMTLIBTheoryAtom>> orList =
                new ArrayList<Formula<SMTLIBTheoryAtom>>(setRepresentation.size());
            for (final Set<Pair<FunctionSymbol, Integer>> set : setRepresentation) {
                final List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(set.size());
                for (final Pair<FunctionSymbol, Integer> pair : set) {
                    final FunctionSymbol sym = pair.x;
                    final int num = pair.y.intValue();
                    final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> params = funToVarsMap.get(sym);
                    andList.add(formFactory.buildNot(formFactory.buildTheoryAtom(params.get(num).y)));
                }
                orList.add(formFactory.buildAnd(andList));
            }
            // Build formula
            final Formula<SMTLIBTheoryAtom> or = formFactory.buildOr(orList);
            formList.add(formFactory.buildImplication(or, formFactory.buildTheoryAtom(ge)));
        }
        for (final Constraint<TRSTerm> c : cons) {
            aborter.checkAbortion();
            count++;
            final TRSTerm l = c.getLeft();
            final TRSTerm r = c.getRight();
            // Collect values for l
            final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMapL =
                new LinkedHashMap<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>>();
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantValsL =
                new LinkedList<Pair<SMTLIBIntValue, SMTLIBBoolValue>>();
            this.buildVarToValMap(l, funToVarsMap, funToConsMap, varToValMapL, constantValsL, ArcticPOLOSolver.arcticOne, vgI, vgB, formList,
                formFactory);
            // Collect values for r
            final Map<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>> varToValMapR =
                new LinkedHashMap<TRSVariable, List<Pair<SMTLIBIntValue, SMTLIBBoolValue>>>();
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> constantValsR =
                new LinkedList<Pair<SMTLIBIntValue, SMTLIBBoolValue>>();
            this.buildVarToValMap(r, funToVarsMap, funToConsMap, varToValMapR, constantValsR, ArcticPOLOSolver.arcticOne, vgI, vgB, formList,
                formFactory);

            final OrderRelation rel = c.getType();
            if (rel.equals(OrderRelation.GE)) {
                final SMTLIBBoolVariable ge = SMTLIBBoolVariable.create("ge" + count);
                formList.add(this.addGE(ge, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, vgI, vgB,
                    formList, formFactory));
                formList.add(formFactory.buildTheoryAtom(ge));
            } else if (rel.equals(OrderRelation.GR)) {
                final SMTLIBBoolVariable gt = SMTLIBBoolVariable.create("gt" + count);
                formList.add(this.addGT(gt, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, vgI, vgB,
                    formList, formFactory));
                formList.add(formFactory.buildTheoryAtom(gt));
            } else if (rel.equals(OrderRelation.EQ)) {
                if (!l.equals(r)) {
                    formList.add(formFactory.buildTheoryAtom(SMTLIBBoolFalse.create()));
                }
            } else {
                // Not supported
                return null;
            }
        }

        if (!nonStrict.isEmpty()) {
            // Encode one-greater constraint for RRR and MRR
            formList.add(formFactory.buildOr(nonStrictGTs));
        }

        // TODO
        //System.err.println(smtInput);

        // Call the SMT checker
        YNM res;
        try {
            res = this.smtChecker.satisfiable(formList, SMTLogic.QF_LIA, aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Solver error: " + e.getErrorMessage());
            res = YNM.MAYBE;
        }

        if (res != YNM.YES) {
            return null;
        }

        final Map<FunctionSymbol, Pair<BigInteger, Boolean>> weightMap =
            new LinkedHashMap<FunctionSymbol, Pair<BigInteger, Boolean>>(symSet.size());
        final Map<FunctionSymbol, List<Pair<BigInteger, Boolean>>> paramMap =
            new LinkedHashMap<FunctionSymbol, List<Pair<BigInteger, Boolean>>>(symSet.size());
        for (final FunctionSymbol sym : symSet) {
            final int arity = sym.getArity();
            final Pair<SMTLIBIntValue, SMTLIBBoolValue> pair = funToConsMap.get(sym);
            final SMTLIBIntVariable v = (SMTLIBIntVariable) pair.x;
            final SMTLIBBoolVariable b = (SMTLIBBoolVariable) pair.y;
            final BigInteger weightI = v.getResultAsBigInteger();
            final Boolean weightB = b.getResultAsBoolean();
            if (weightI == null || weightB == null) {
                weightMap.put(sym, new Pair<BigInteger, Boolean>(BigInteger.ZERO, Boolean.TRUE));
            } else {
                weightMap.put(sym, new Pair<BigInteger, Boolean>(weightI, weightB));
            }
            final List<Pair<SMTLIBIntValue, SMTLIBBoolValue>> vals = funToVarsMap.get(sym);
            final List<Pair<BigInteger, Boolean>> arr = new ArrayList<Pair<BigInteger, Boolean>>(arity);
            for (final Pair<SMTLIBIntValue, SMTLIBBoolValue> val : vals) {
                final SMTLIBIntVariable iv = (SMTLIBIntVariable) val.x;
                final SMTLIBBoolVariable bv = (SMTLIBBoolVariable) val.y;
                final BigInteger iRes = iv.getResultAsBigInteger();
                final Boolean bRes = bv.getResultAsBoolean();
                if (iRes != null && bRes != null) {
                    arr.add(new Pair<BigInteger, Boolean>(iRes, bRes));
                } else {
                    arr.add(new Pair<BigInteger, Boolean>(BigInteger.ZERO, Boolean.TRUE));
                }
            }
            paramMap.put(sym, arr);
        }

        final ArcticPOLO result = ArcticPOLO.create(weightMap, paramMap, symSet);

        return result;
    }
}
