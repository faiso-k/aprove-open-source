package aprove.verification.dpframework.Orders.Solvers;

import java.math.*;
import java.util.*;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.SMTUtility.*;
import immutables.*;

/**
 * SMT based solver for linear polynomial orderings
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class LinearPOLOSolver implements AbortableConstraintSolver<TRSTerm> {

    private SMTEngine smtChecker = null;

    private int numBits = 0;
    private boolean isMonotone = true;

    private FullSharingFlatteningFactory<SMTLIBTheoryAtom> formFactory;

    public LinearPOLOSolver(SMTEngine smtChecker, AFSType afsType, int numBits) {
        this.smtChecker = smtChecker;
        switch (afsType) {
        case NOAFS:
        case MONOTONEAFS:
            this.isMonotone = true;
            break;
        case FULLAFS:
            this.isMonotone = false;
            break;
        default:
            throw new UnsupportedOperationException("Unknown AFS type!");
        }
        this.numBits = numBits;
        if (numBits <= 0) {
            throw new UnsupportedOperationException("coeffients' length must be at least 1");
        }
        this.formFactory = new FullSharingFlatteningFactory<SMTLIBTheoryAtom>();
    }

    // Define multiplication a*b
    // of an integer value a and a
    // bitvector-representation b
    // The result is an integer value
    private Formula<SMTLIBTheoryAtom> multBVItoI(SMTLIBIntValue a, SMTLIBBVValue b, SMTLIBIntValue c, int maxBVlen) {
        List<SMTLIBIntValue> plusList = new ArrayList<SMTLIBIntValue>(maxBVlen);
        SMTLIBIntConstant iZero = SMTLIBIntConstant.create(BigInteger.ZERO);
        int factor = 1;
        for (int i = 0; i < maxBVlen; i++) {
            SMTLIBIntConstant iFactor = SMTLIBIntConstant.create(BigInteger.valueOf(factor));
            SMTLIBBVConstant bvFactor = SMTLIBBVConstant.create(BigInteger.valueOf(factor), maxBVlen);
            List<SMTLIBIntValue> multList = new ArrayList<SMTLIBIntValue>(2);
            multList.add(iFactor);
            multList.add(a);
            SMTLIBIntMult mult = SMTLIBIntMult.create(multList);
            SMTLIBBVAnd and = SMTLIBBVAnd.create(bvFactor, b);
            SMTLIBBVEquals eq = SMTLIBBVEquals.create(and, bvFactor);
            SMTLIBIntITE ite = SMTLIBIntITE.create(eq, mult, iZero);
            plusList.add(ite);
            factor *= 2;
        }
        SMTLIBIntEquals eq = SMTLIBIntEquals.create(c, SMTLIBIntPlus.create(plusList));
        return this.formFactory.buildTheoryAtom(eq);
    }

    // Define a nat variable for a given bitvector
    private Formula<SMTLIBTheoryAtom> convertBVtoI(SMTLIBBVValue bvVal, SMTLIBIntValue iVal, int maxBVlen) {
        SMTLIBIntConstant iZero = SMTLIBIntConstant.create(BigInteger.ZERO);
        int factor = 1;
        List<SMTLIBIntValue> plusList = new ArrayList<SMTLIBIntValue>(maxBVlen);
        for (int i = 0; i < maxBVlen; i++) {
            SMTLIBIntConstant iFactor = SMTLIBIntConstant.create(BigInteger.valueOf(factor));
            SMTLIBBVConstant bvFactor = SMTLIBBVConstant.create(BigInteger.valueOf(factor), maxBVlen);
            SMTLIBBVAnd and = SMTLIBBVAnd.create(bvVal, bvFactor);
            SMTLIBBVEquals eq = SMTLIBBVEquals.create(and, bvFactor);
            SMTLIBIntITE ite = SMTLIBIntITE.create(eq, iFactor, iZero);
            plusList.add(ite);
            factor *= 2;
        }
        SMTLIBIntEquals eq = SMTLIBIntEquals.create(iVal, SMTLIBIntPlus.create(plusList));
        return this.formFactory.buildTheoryAtom(eq);
    }

    private void buildVarToValMap(TRSTerm t, Set<FunctionSymbol> symSet,
            Map<FunctionSymbol, List<SMTLIBBVValue>> symToParamsMap,
            Map<FunctionSymbol, SMTLIBIntValue> symToConsMap,
            Map<TRSVariable, List<SMTLIBIntValue>> varToValMap, List<SMTLIBIntValue> constantVals,
            SMTLIBBVValue bvParam, int maxBVlen,
            SMTLIBIntVariableGenerator vgI, SMTLIBBVVariableGenerator vgBV,
            List<Formula<SMTLIBTheoryAtom>> formList) {

        if (t.isVariable()) {
            TRSVariable vt = (TRSVariable)t;
            List<SMTLIBIntValue> values = varToValMap.get(vt);
            if (values == null) {
                values = new LinkedList<SMTLIBIntValue>();
                varToValMap.put(vt, values);
            }
            SMTLIBIntVariable iNew = vgI.getNewVariable();
            formList.add(this.convertBVtoI(bvParam, iNew, maxBVlen));
            values.add(iNew);

        } else {
            TRSFunctionApplication fat = (TRSFunctionApplication)t;
            FunctionSymbol symt = fat.getRootSymbol();
            SMTLIBIntValue cons = symToConsMap.get(symt);
            List<SMTLIBBVValue> params = symToParamsMap.get(symt);
            // Collect constant value
            SMTLIBIntVariable iNew = vgI.getNewVariable();
            formList.add(this.multBVItoI(cons, bvParam, iNew, maxBVlen));
            constantVals.add(iNew);
            // Collect values for the parameters
            int i = 0;
            for (SMTLIBBVValue v : params) {
                SMTLIBBVVariable bvNew = vgBV.getNewVariable();
                SMTLIBBVMul mult = SMTLIBBVMul.create(v, bvParam);
                SMTLIBBVEquals eq = SMTLIBBVEquals.create(bvNew, mult);
                formList.add(this.formFactory.buildTheoryAtom(eq));

                this.buildVarToValMap(fat.getArgument(i), symSet, symToParamsMap, symToConsMap, varToValMap, constantVals, bvNew, maxBVlen, vgI, vgBV, formList);
                i++;
            }
        }
    }


    // Encode GREATER EQUAL
    private Formula<SMTLIBTheoryAtom> addGE(SMTLIBBoolVariable var, Set<TRSVariable> varSet, Map<TRSVariable, List<SMTLIBIntValue>> varToValMapL, List<SMTLIBIntValue> constantValsL, Map<TRSVariable, List<SMTLIBIntValue>> varToValMapR, List<SMTLIBIntValue> constantValsR, int maxBVlen) {
        List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(varSet.size()+1);
        SMTLIBIntConstant iZero = SMTLIBIntConstant.create(BigInteger.ZERO);
        // Compare constant values
        SMTLIBIntValue consL;
        if (constantValsL.isEmpty()) {
            consL = iZero;
        } else {
            consL = SMTLIBIntPlus.create(constantValsL);
        }
        SMTLIBIntValue consR;
        if (constantValsR.isEmpty()) {
            consR = iZero;
        } else {
            consR = SMTLIBIntPlus.create(constantValsR);
        }

        SMTLIBIntGE consGE = SMTLIBIntGE.create(consL, consR);
        andList.add(this.formFactory.buildTheoryAtom(consGE));

        // Compare variables
        for (TRSVariable v : varSet) {
            List<SMTLIBIntValue> valsL = varToValMapL.get(v);
            SMTLIBIntValue varL;
            if (valsL == null) {
                varL = iZero;
            } else if (valsL.isEmpty()) {
                varL = iZero;
            } else {
                varL = SMTLIBIntPlus.create(valsL);
            }
            List<SMTLIBIntValue> valsR = varToValMapR.get(v);
            SMTLIBIntValue varR;
            if (valsR == null) {
                varR = iZero;
            } else if (valsR.isEmpty()) {
                varR = iZero;
            } else {
                varR = SMTLIBIntPlus.create(valsR);
            }

            SMTLIBIntGE varGE = SMTLIBIntGE.create(varL, varR);
            andList.add(this.formFactory.buildTheoryAtom(varGE));
        }
        return this.formFactory.buildIff(this.formFactory.buildTheoryAtom(var), this.formFactory.buildAnd(andList));
    }

    // Encode GREATER THAN
    private Formula<SMTLIBTheoryAtom> addGT(SMTLIBBoolVariable var, Set<TRSVariable> varSet, Map<TRSVariable, List<SMTLIBIntValue>> varToValMapL, List<SMTLIBIntValue> constantValsL, Map<TRSVariable, List<SMTLIBIntValue>> varToValMapR, List<SMTLIBIntValue> constantValsR, int maxBVlen) {
        List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(varSet.size()+1);
        SMTLIBIntConstant iZero = SMTLIBIntConstant.create(BigInteger.ZERO);
        // Compare constant values
        SMTLIBIntValue consL;
        if (constantValsL.isEmpty()) {
            consL = iZero;
        } else {
            consL = SMTLIBIntPlus.create(constantValsL);
        }
        SMTLIBIntValue consR;
        if (constantValsR.isEmpty()) {
            consR = iZero;
        } else {
            consR = SMTLIBIntPlus.create(constantValsR);
        }

        SMTLIBIntGT consGT = SMTLIBIntGT.create(consL, consR);
        andList.add(this.formFactory.buildTheoryAtom(consGT));

        // Compare variables
        for (TRSVariable v : varSet) {
            List<SMTLIBIntValue> valsL = varToValMapL.get(v);
            SMTLIBIntValue varL;
            if (valsL == null) {
                varL = iZero;
            } else if (valsL.isEmpty()) {
                varL = iZero;
            } else {
                varL = SMTLIBIntPlus.create(valsL);
            }
            List<SMTLIBIntValue> valsR = varToValMapR.get(v);
            SMTLIBIntValue varR;
            if (valsR == null) {
                varR = iZero;
            } else if (valsR.isEmpty()) {
                varR = iZero;
            } else {
                varR = SMTLIBIntPlus.create(valsR);
            }

            SMTLIBIntGE varGE = SMTLIBIntGE.create(varL, varR);
            andList.add(this.formFactory.buildTheoryAtom(varGE));
        }
        return this.formFactory.buildIff(this.formFactory.buildTheoryAtom(var), this.formFactory.buildAnd(andList));
    }

    private int getMaxBVlen(Collection<Constraint<TRSTerm>> cs) {
        int maxLen = 0;
        for (Constraint<TRSTerm> c : cs) {
            int lLen = c.getLeft().getDepth();
            int rLen = c.getRight().getDepth();
            int curLen = (lLen > rLen)?lLen:rLen;
            if (curLen > maxLen) {
                maxLen = curLen;
            }
        }
        return maxLen * this.numBits + 1;
    }

    // Solve constraints only
    @Override
    public final ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> constraints, Abortion aborter) throws AbortionException {
        return this.solve(constraints, null, aborter);
    }

    // Solve constraints and non-strict rules
    public POLO solve(Collection<Constraint<TRSTerm>> cons, Set<Rule> nonStrict, Abortion aborter)
    throws AbortionException {
        return this.solve(null, cons, nonStrict, null, aborter);
    }

    // Solve constraints and non-strict rules w.r.t. mu
    public POLO solve(Collection<Constraint<TRSTerm>> cons, Set<Rule> nonStrict, ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu, Abortion aborter)
    throws AbortionException {
        return this.solve(null, cons, nonStrict, mu, aborter);
    }

    // Solve constraints and non-strict rules w.r.t. mu and Q active conditions
    public POLO solve(Map<? extends GeneralizedRule, QActiveCondition> R, Collection<Constraint<TRSTerm>> cons, Set<? extends GeneralizedRule> nonStrict, ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu, Abortion aborter)
            throws AbortionException {

        if (cons == null) {
            cons = new LinkedHashSet<Constraint<TRSTerm>>();
        }
        if (nonStrict == null) {
            nonStrict = new LinkedHashSet<Rule>();
        }
        if (R == null) {
            R = new LinkedHashMap<Rule, QActiveCondition>();
        }
        Collection<Constraint<TRSTerm>> cs = new LinkedHashSet<Constraint<TRSTerm>>(cons);

        for (GeneralizedRule rule : nonStrict) {
            cs.add(Constraint.fromRule(rule, OrderRelation.GE));
        }
        for (Map.Entry<? extends GeneralizedRule, QActiveCondition> e : R.entrySet()) {
            cs.add(Constraint.fromRule(e.getKey(), OrderRelation.GE));
        }
        int maxBVlen = this.getMaxBVlen(cs);


        // Create variable maps
        Set<FunctionSymbol> symSet = Constraint.getFunctionSymbols(cs);
        Map<FunctionSymbol, SMTLIBIntValue> funToConsMap = new LinkedHashMap<FunctionSymbol, SMTLIBIntValue>();
        Map<FunctionSymbol, List<SMTLIBBVValue>> funToVarsMap = new LinkedHashMap<FunctionSymbol, List<SMTLIBBVValue>>();

        for (FunctionSymbol sym : symSet) {
            int arity = sym.getArity();
            String symName = sym.getName();
            // Define variable for constant value
            SMTLIBIntVariable v = SMTLIBIntVariable.create("cons_"+arity+"_"+symName);
            funToConsMap.put(sym, v);
            // Define variables for parameters
            List<SMTLIBBVValue> paramList = new ArrayList<SMTLIBBVValue>(arity);
            for (int i = 0; i < arity; i++) {
                paramList.add(SMTLIBBVVariable.create("param_"+arity+"_"+symName+"_"+i, maxBVlen));
            }
            funToVarsMap.put(sym, paramList);
        }
        Set<TRSVariable> varSet = Constraint.getVariables(cs);

        aborter.checkAbortion();

        // Encode general constraints
        int maximum = 1;
        for (int i = 0; i < this.numBits; i++) {
            maximum *= 2;
        }
        SMTLIBBVValue bvZero = SMTLIBBVConstant.create(BigInteger.ZERO, maxBVlen);
        SMTLIBIntValue iZero = SMTLIBIntConstant.create(BigInteger.ZERO);
        SMTLIBBVValue bvMax = SMTLIBBVConstant.create(BigInteger.valueOf(maximum), maxBVlen);
        List<Formula<SMTLIBTheoryAtom>> formList = new LinkedList<Formula<SMTLIBTheoryAtom>>();
        for (FunctionSymbol sym : symSet) {
            int arity = sym.getArity();
            List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(arity+2);
            SMTLIBIntValue val = funToConsMap.get(sym);
            andList.add(this.formFactory.buildTheoryAtom(SMTLIBIntGE.create(val, iZero)));
            List<SMTLIBBVValue> vals = funToVarsMap.get(sym);
            if (this.isMonotone) {
                if (mu == null) {
                    for (SMTLIBBVValue v : vals) {
                        // parameter coefficients may not be 0 if monotonicity is required
                        andList.add(this.formFactory.buildTheoryAtom(SMTLIBBVGT.create(v, bvZero)));
                    }
                } else {
                    Set<Integer> intSet = mu.get(sym);
                    if (intSet != null) {
                        // Define mu-monotonicity
                        for (Integer i : intSet) {
                            andList.add(this.formFactory.buildTheoryAtom(SMTLIBBVGT.create(vals.get(i), bvZero)));
                        }
                    } else {
                        for (SMTLIBBVValue v : vals) {
                            // parameter coefficients may not be 0 if monotonicity is required
                            andList.add(this.formFactory.buildTheoryAtom(SMTLIBBVGT.create(v, bvZero)));
                        }
                    }
                }
            }
            for (SMTLIBBVValue v : vals) {
                // param is smaller than 2^numBits
                andList.add(this.formFactory.buildTheoryAtom(SMTLIBBVLT.create(v, bvMax)));
            }
            formList.add(this.formFactory.buildAnd(andList));
        }

        // Encode first bitvector for 1
        SMTLIBBVConstant bvOne = SMTLIBBVConstant.create(BigInteger.ONE, maxBVlen);


        SMTLIBIntVariableGenerator vgI = SMTLIBIntVariableGenerator.create("int");
        SMTLIBBVVariableGenerator vgBV = SMTLIBBVVariableGenerator.create("bv", maxBVlen);

        List<Formula<SMTLIBTheoryAtom>> nonStrictGTs = new ArrayList<Formula<SMTLIBTheoryAtom>>(nonStrict.size());
        // Encode linear poly constraints
        int count = 0;
        for (GeneralizedRule rule : nonStrict) {
            aborter.checkAbortion();
            count++;
            TRSTerm l = rule.getLeft();
            TRSTerm r = rule.getRight();
            // Collect values for l
            Map<TRSVariable, List<SMTLIBIntValue>> varToValMapL = new LinkedHashMap<TRSVariable, List<SMTLIBIntValue>>();
            List<SMTLIBIntValue> constantValsL = new LinkedList<SMTLIBIntValue>();
            this.buildVarToValMap(l, symSet, funToVarsMap, funToConsMap, varToValMapL, constantValsL, bvOne, maxBVlen, vgI, vgBV, formList);
            // Collect values for r
            Map<TRSVariable, List<SMTLIBIntValue>> varToValMapR = new LinkedHashMap<TRSVariable, List<SMTLIBIntValue>>();
            List<SMTLIBIntValue> constantValsR = new LinkedList<SMTLIBIntValue>();
            this.buildVarToValMap(r, symSet, funToVarsMap, funToConsMap, varToValMapR, constantValsR, bvOne, maxBVlen, vgI, vgBV, formList);

            // Encode and define gr and ge constraint
            SMTLIBBoolVariable gt = SMTLIBBoolVariable.create("gt"+count);
            formList.add(this.addGT(gt, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, maxBVlen));
            nonStrictGTs.add(this.formFactory.buildTheoryAtom(gt));
            SMTLIBBoolVariable ge = SMTLIBBoolVariable.create("ge"+count);
            formList.add(this.addGE(ge, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, maxBVlen));
            formList.add(this.formFactory.buildTheoryAtom(ge));
        }
        for (Map.Entry<? extends GeneralizedRule, QActiveCondition> e : R.entrySet()) {
            count++;
            GeneralizedRule rule = e.getKey();
            TRSTerm l = rule.getLeft();
            TRSTerm r = rule.getRight();
            // Collect values for l
            Map<TRSVariable, List<SMTLIBIntValue>> varToValMapL = new LinkedHashMap<TRSVariable, List<SMTLIBIntValue>>();
            List<SMTLIBIntValue> constantValsL = new LinkedList<SMTLIBIntValue>();
            this.buildVarToValMap(l, symSet, funToVarsMap, funToConsMap, varToValMapL, constantValsL, bvOne, maxBVlen, vgI, vgBV, formList);
            // Collect values for r
            Map<TRSVariable, List<SMTLIBIntValue>> varToValMapR = new LinkedHashMap<TRSVariable, List<SMTLIBIntValue>>();
            List<SMTLIBIntValue> constantValsR = new LinkedList<SMTLIBIntValue>();
            this.buildVarToValMap(r, symSet, funToVarsMap, funToConsMap, varToValMapR, constantValsR, bvOne, maxBVlen, vgI, vgBV, formList);

            // Encode and define ge constraint
            SMTLIBBoolVariable ge = SMTLIBBoolVariable.create("ge"+count);
            formList.add(this.addGE(ge, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, maxBVlen));


            // Encode Q active constraint
            QActiveCondition qac = e.getValue();
            Set<? extends Set<Pair<FunctionSymbol, Integer>>> setRepresentation = qac.getSetRepresentation();

            List<Formula<SMTLIBTheoryAtom>> orList = new ArrayList<Formula<SMTLIBTheoryAtom>>(setRepresentation.size());
            for (Set<Pair<FunctionSymbol, Integer>> set :  setRepresentation) {
                List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(set.size());
                for (Pair<FunctionSymbol, Integer> pair : set) {
                    FunctionSymbol sym = pair.x;
                    int num = pair.y.intValue();
                    List<SMTLIBBVValue> params = funToVarsMap.get(sym);
                    SMTLIBBVGT gt = SMTLIBBVGT.create(params.get(num), bvZero);
                    andList.add(this.formFactory.buildTheoryAtom(gt));
                }
                orList.add(this.formFactory.buildAnd(andList));
            }
            // Build formula
            Formula<SMTLIBTheoryAtom> or = this.formFactory.buildOr(orList);
            formList.add(this.formFactory.buildImplication(or, this.formFactory.buildTheoryAtom(ge)));
        }
        for (Constraint<TRSTerm> c : cons) {
            aborter.checkAbortion();
            count++;
            TRSTerm l = c.getLeft();
            TRSTerm r = c.getRight();
            // Collect values for l
            Map<TRSVariable, List<SMTLIBIntValue>> varToValMapL = new LinkedHashMap<TRSVariable, List<SMTLIBIntValue>>();
            List<SMTLIBIntValue> constantValsL = new LinkedList<SMTLIBIntValue>();
            this.buildVarToValMap(l, symSet, funToVarsMap, funToConsMap, varToValMapL, constantValsL, bvOne, maxBVlen, vgI, vgBV, formList);
            // Collect values for r
            Map<TRSVariable, List<SMTLIBIntValue>> varToValMapR = new LinkedHashMap<TRSVariable, List<SMTLIBIntValue>>();
            List<SMTLIBIntValue> constantValsR = new LinkedList<SMTLIBIntValue>();
            this.buildVarToValMap(r, symSet, funToVarsMap, funToConsMap, varToValMapR, constantValsR, bvOne, maxBVlen, vgI, vgBV, formList);

            OrderRelation rel = c.getType();
            if (rel.equals(OrderRelation.GE)) {
                SMTLIBBoolVariable ge = SMTLIBBoolVariable.create("ge"+count);
                formList.add(this.addGE(ge, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, maxBVlen));
                formList.add(this.formFactory.buildTheoryAtom(ge));
            } else if (rel.equals(OrderRelation.GR)) {
                SMTLIBBoolVariable gt = SMTLIBBoolVariable.create("gt"+count);
                formList.add(this.addGT(gt, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, maxBVlen));
                formList.add(this.formFactory.buildTheoryAtom(gt));
            } else if (rel.equals(OrderRelation.EQ)) {
                if (!l.equals(r)) {
                    formList.add(this.formFactory.buildTheoryAtom(SMTLIBBoolFalse.create()));
                }
            } else {
                // Not supported
                return null;
            }
        }

        if (!nonStrict.isEmpty()) {
            // Encode one-greater constraint for RRR and MRR
            formList.add(this.formFactory.buildOr(nonStrictGTs));
        }

        // TODO
        //System.err.println(smtInput);

        // Call the SMT checker
        YNM res;
        try {
            res = this.smtChecker.satisfiable(formList, SMTLogic.QF_BV, aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Solver error: " + e.getErrorMessage());
            res = YNM.MAYBE;
        }

        if (res != YNM.YES) {
            return null;
        }

        Map<FunctionSymbol, BigInteger> weightMap = new LinkedHashMap<FunctionSymbol, BigInteger>(symSet.size());
        Map<FunctionSymbol, int[]> paramMap = new LinkedHashMap<FunctionSymbol, int[]>(symSet.size());
        for (FunctionSymbol sym : symSet) {
            int arity = sym.getArity();
            SMTLIBIntVariable v = (SMTLIBIntVariable)funToConsMap.get(sym);
            BigInteger weight = v.getResultAsBigInteger();
            if (weight == null) {
                weightMap.put(sym, BigInteger.ZERO);
            } else {
                weightMap.put(sym, weight);
            }
            List<SMTLIBBVValue> vals = funToVarsMap.get(sym);
            int[] arr = new int[arity];
            int i = 0;
            for (SMTLIBBVValue val : vals) {
                SMTLIBBVVariable bv = (SMTLIBBVVariable)val;
                Integer iRes = bv.getResultAsUnsignedInteger();
                if (iRes != 0) {
                    arr[i] = iRes.intValue();
                }
                i++;
            }
            paramMap.put(sym, arr);
        }

        // Create POLO interpretation
        Interpretation inter = Interpretation.create();
        List<IndefinitePart> varParts = new ArrayList<IndefinitePart>();

        for (FunctionSymbol sym: symSet) {
            int arity = sym.getArity();

            // update cache
            int size = varParts.size();
            for (int i = size + 1; i <= arity; ++i) {
                // the i-th argument of f (at argument position i-1)
                // is represented by x_i
                String newVar = Interpretation.VARIABLE_PREFIX + i;
                IndefinitePart newVarPart = IndefinitePart.create(newVar, 1);
                varParts.add(newVarPart);
            }

            // build map variable -> coeff for poly
            Map<IndefinitePart, SimplePolynomial> varMonomials
                = new LinkedHashMap<IndefinitePart, SimplePolynomial>(arity+1);
            int[] arr = paramMap.get(sym);
            for (int i = 0; i < arity; ++i) {
                if (arr[i] != 0) {
                    IndefinitePart varPart = varParts.get(i);
                    varMonomials.put(varPart, SimplePolynomial.create(arr[i]));
                }
            }

            // add constant if it is != 0 (VarPolys do not take
            // addends that amount to zero)
            BigInteger weight = weightMap.get(sym);
            if (weight.signum() != 0) {
                SimplePolynomial weightPoly = SimplePolynomial.create(weight);
                varMonomials.put(IndefinitePart.ONE, weightPoly);
            }

            // finally assemble the polynomial interpretation for f
            ImmutableMap<IndefinitePart, SimplePolynomial> immutableVarMonomials
                = ImmutableCreator.create(varMonomials);
            VarPolynomial fInter = VarPolynomial.create(immutableVarMonomials);
            inter.put(sym, fInter);
        }
        POLO polo = POLO.create(inter);
        return polo;
    }


}
