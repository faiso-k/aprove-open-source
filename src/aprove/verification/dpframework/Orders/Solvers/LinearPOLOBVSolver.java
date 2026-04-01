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
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.SMTUtility.*;
import immutables.*;

/**
 * SMT based solver for linear polynomial orderings
 * This solver uses only bitvectors, not integers
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class LinearPOLOBVSolver implements AbortableConstraintSolver<TRSTerm> {

    private SMTEngine smtChecker = null;

    private int numBits = 0;
    private boolean isMonotone = true;

    private FullSharingFlatteningFactory<SMTLIBTheoryAtom> formFactory;

    public LinearPOLOBVSolver(SMTEngine smtChecker, AFSType afsType, int numBits) {
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

    private void buildVarToValMap(TRSTerm t, Set<FunctionSymbol> symSet,
            Map<FunctionSymbol, List<SMTLIBBVValue>> symToParamsMap,
            Map<FunctionSymbol, SMTLIBBVValue> symToConsMap,
            Map<TRSVariable, List<SMTLIBBVValue>> varToValMap, List<SMTLIBBVValue> constantVals,
            SMTLIBBVValue bvParam, int maxBVlen,
            SMTLIBBVVariableGenerator vgBV,
            List<Formula<SMTLIBTheoryAtom>> formList) {

        if (t.isVariable()) {
            TRSVariable vt = (TRSVariable)t;
            List<SMTLIBBVValue> values = varToValMap.get(vt);
            if (values == null) {
                values = new LinkedList<SMTLIBBVValue>();
                varToValMap.put(vt, values);
            }
            values.add(bvParam);

        } else {
            TRSFunctionApplication fat = (TRSFunctionApplication)t;
            FunctionSymbol symt = fat.getRootSymbol();
            SMTLIBBVValue cons = symToConsMap.get(symt);
            List<SMTLIBBVValue> params = symToParamsMap.get(symt);
            // Collect constant value
            SMTLIBBVVariable bvCons = vgBV.getNewVariable();
            SMTLIBBVMul multCons = SMTLIBBVMul.create(cons, bvParam);
            SMTLIBBVEquals eqCons = SMTLIBBVEquals.create(bvCons, multCons);
            formList.add(this.formFactory.buildTheoryAtom(eqCons));

            constantVals.add(multCons);
            // Collect values for the parameters
            int i = 0;
            for (SMTLIBBVValue v : params) {
                SMTLIBBVVariable bvNew = vgBV.getNewVariable();
                SMTLIBBVMul mult = SMTLIBBVMul.create(v, bvParam);
                SMTLIBBVEquals eq = SMTLIBBVEquals.create(bvNew, mult);
                formList.add(this.formFactory.buildTheoryAtom(eq));

                this.buildVarToValMap(fat.getArgument(i), symSet, symToParamsMap, symToConsMap, varToValMap, constantVals, bvNew, maxBVlen, vgBV, formList);
                i++;
            }
        }
    }


    // Encode GREATER EQUAL
    private Formula<SMTLIBTheoryAtom> addGE(SMTLIBBoolVariable var, Set<TRSVariable> varSet, Map<TRSVariable, List<SMTLIBBVValue>> varToValMapL, List<SMTLIBBVValue> constantValsL, Map<TRSVariable, List<SMTLIBBVValue>> varToValMapR, List<SMTLIBBVValue> constantValsR, int maxBVlen) {
        List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(varSet.size()+1);
        SMTLIBBVConstant bvZero = SMTLIBBVConstant.create(BigInteger.ZERO, maxBVlen);
        // Compare constant values
        SMTLIBBVValue consL;
        if (constantValsL.isEmpty()) {
            consL = bvZero;
        } else {
            SMTLIBBVValue cur = bvZero;
            for (SMTLIBBVValue val : constantValsL) {
                cur = SMTLIBBVAdd.create(cur, val);
            }
            consL = cur;
        }
        SMTLIBBVValue consR;
        if (constantValsR.isEmpty()) {
            consR = bvZero;
        } else {
            SMTLIBBVValue cur = bvZero;
            for (SMTLIBBVValue val : constantValsR) {
                cur = SMTLIBBVAdd.create(cur, val);
            }
            consR = cur;
        }
        SMTLIBBVGE consGE = SMTLIBBVGE.create(consL, consR);
        andList.add(this.formFactory.buildTheoryAtom(consGE));

        // Compare variables
        for (TRSVariable v : varSet) {
            List<SMTLIBBVValue> valsL = varToValMapL.get(v);
            SMTLIBBVValue varL;
            if (valsL == null) {
                varL = bvZero;
            } else if (valsL.isEmpty()) {
                varL = bvZero;
            } else {
                SMTLIBBVValue cur = bvZero;
                for (SMTLIBBVValue val : valsL) {
                    cur = SMTLIBBVAdd.create(cur, val);
                }
                varL = cur;
            }
            List<SMTLIBBVValue> valsR = varToValMapR.get(v);
            SMTLIBBVValue varR;
            if (valsR == null) {
                varR = bvZero;
            } else if (valsR.isEmpty()) {
                varR = bvZero;
            } else {
                SMTLIBBVValue cur = bvZero;
                for (SMTLIBBVValue val : valsR) {
                    cur = SMTLIBBVAdd.create(cur, val);
                }
                varR = cur;
            }

            SMTLIBBVGE varGE = SMTLIBBVGE.create(varL, varR);
            andList.add(this.formFactory.buildTheoryAtom(varGE));
        }
        return this.formFactory.buildIff(this.formFactory.buildTheoryAtom(var), this.formFactory.buildAnd(andList));
    }

    // Encode GREATER THAN
    private Formula<SMTLIBTheoryAtom> addGT(SMTLIBBoolVariable var, Set<TRSVariable> varSet, Map<TRSVariable, List<SMTLIBBVValue>> varToValMapL, List<SMTLIBBVValue> constantValsL, Map<TRSVariable, List<SMTLIBBVValue>> varToValMapR, List<SMTLIBBVValue> constantValsR, int maxBVlen) {
        List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(varSet.size()+1);
        SMTLIBBVConstant bvZero = SMTLIBBVConstant.create(BigInteger.ZERO, maxBVlen);
        // Compare constant values
        SMTLIBBVValue consL;
        if (constantValsL.isEmpty()) {
            consL = bvZero;
        } else {
            SMTLIBBVValue cur = bvZero;
            for (SMTLIBBVValue val : constantValsL) {
                cur = SMTLIBBVAdd.create(cur, val);
            }
            consL = cur;
        }
        SMTLIBBVValue consR;
        if (constantValsR.isEmpty()) {
            consR = bvZero;
        } else {
            SMTLIBBVValue cur = bvZero;
            for (SMTLIBBVValue val : constantValsR) {
                cur = SMTLIBBVAdd.create(cur, val);
            }
            consR = cur;
        }
        SMTLIBBVGT consGT = SMTLIBBVGT.create(consL, consR);
        andList.add(this.formFactory.buildTheoryAtom(consGT));

        // Compare variables
        for (TRSVariable v : varSet) {
            List<SMTLIBBVValue> valsL = varToValMapL.get(v);
            SMTLIBBVValue varL;
            if (valsL == null) {
                varL = bvZero;
            } else if (valsL.isEmpty()) {
                varL = bvZero;
            } else {
                SMTLIBBVValue cur = bvZero;
                for (SMTLIBBVValue val : valsL) {
                    cur = SMTLIBBVAdd.create(cur, val);
                }
                varL = cur;
            }
            List<SMTLIBBVValue> valsR = varToValMapR.get(v);
            SMTLIBBVValue varR;
            if (valsR == null) {
                varR = bvZero;
            } else if (valsR.isEmpty()) {
                varR = bvZero;
            } else {
                SMTLIBBVValue cur = bvZero;
                for (SMTLIBBVValue val : valsR) {
                    cur = SMTLIBBVAdd.create(cur, val);
                }
                varR = cur;
            }

            SMTLIBBVGE varGE = SMTLIBBVGE.create(varL, varR);
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
        maxLen++;
        maxLen *= this.numBits;
        maxLen += Constraint.getVariables(cs).size();
        return maxLen + 1;
    }

    @Override
    public final ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> constraints, Abortion aborter) throws AbortionException {
        return this.solve(constraints, null, aborter);
    }

    public POLO solve(Collection<Constraint<TRSTerm>> cons, Set<Rule> nonStrict, Abortion aborter)
            throws AbortionException {
        return this.solve(null, cons, nonStrict, aborter);
    }

    public POLO solve(Map<Rule, QActiveCondition> R, Collection<Constraint<TRSTerm>> cons, Set<Rule> nonStrict, Abortion aborter)
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

        for (Rule rule : nonStrict) {
            cs.add(Constraint.fromRule(rule, OrderRelation.GE));
        }
        for (Map.Entry<Rule, QActiveCondition> e : R.entrySet()) {
            cs.add(Constraint.fromRule(e.getKey(), OrderRelation.GE));
        }
        int maxBVlen = this.getMaxBVlen(cs);


        // Create variable maps
        Set<FunctionSymbol> symSet = Constraint.getFunctionSymbols(cs);
        Map<FunctionSymbol, SMTLIBBVValue> funToConsMap = new LinkedHashMap<FunctionSymbol, SMTLIBBVValue>();
        Map<FunctionSymbol, List<SMTLIBBVValue>> funToVarsMap = new LinkedHashMap<FunctionSymbol, List<SMTLIBBVValue>>();

        for (FunctionSymbol sym : symSet) {
            int arity = sym.getArity();
            String symName = sym.getName();
            // Define variable for constant value
            SMTLIBBVVariable v = SMTLIBBVVariable.create("cons_"+arity+"_"+symName, maxBVlen);
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
        SMTLIBBVValue bvMax = SMTLIBBVConstant.create(BigInteger.valueOf(maximum), maxBVlen);
        List<Formula<SMTLIBTheoryAtom>> formList = new LinkedList<Formula<SMTLIBTheoryAtom>>();
        for (FunctionSymbol sym : symSet) {
            int arity = sym.getArity();
            List<Formula<SMTLIBTheoryAtom>> andList = new ArrayList<Formula<SMTLIBTheoryAtom>>(arity+2);
            List<SMTLIBBVValue> vals = funToVarsMap.get(sym);
            if (this.isMonotone) {
                for (SMTLIBBVValue v : vals) {
                    // parameter coefficients may not be 0 if monotonicity is required
                    andList.add(this.formFactory.buildTheoryAtom(SMTLIBBVGT.create(v, bvZero)));
                }
            }
            SMTLIBBVValue val = funToConsMap.get(sym);
            andList.add(this.formFactory.buildTheoryAtom(SMTLIBBVLT.create(val, bvMax)));
            for (SMTLIBBVValue v : vals) {
                // param is smaller than 2^numBits
                andList.add(this.formFactory.buildTheoryAtom(SMTLIBBVLT.create(v, bvMax)));
            }
            formList.add(this.formFactory.buildAnd(andList));
        }

        // Encode first bitvector for 1
        SMTLIBBVConstant bvOne = SMTLIBBVConstant.create(BigInteger.ONE, maxBVlen);


        SMTLIBBVVariableGenerator vgBV = SMTLIBBVVariableGenerator.create("bv", maxBVlen);

        List<Formula<SMTLIBTheoryAtom>> nonStrictGTs = new ArrayList<Formula<SMTLIBTheoryAtom>>(nonStrict.size());
        // Encode linear poly constraints
        int count = 0;
        for (Rule rule : nonStrict) {
            aborter.checkAbortion();
            count++;
            TRSTerm l = rule.getLeft();
            TRSTerm r = rule.getRight();
            // Collect values for l
            Map<TRSVariable, List<SMTLIBBVValue>> varToValMapL = new LinkedHashMap<TRSVariable, List<SMTLIBBVValue>>();
            List<SMTLIBBVValue> constantValsL = new LinkedList<SMTLIBBVValue>();
            this.buildVarToValMap(l, symSet, funToVarsMap, funToConsMap, varToValMapL, constantValsL, bvOne, maxBVlen, vgBV, formList);
            // Collect values for r
            Map<TRSVariable, List<SMTLIBBVValue>> varToValMapR = new LinkedHashMap<TRSVariable, List<SMTLIBBVValue>>();
            List<SMTLIBBVValue> constantValsR = new LinkedList<SMTLIBBVValue>();
            this.buildVarToValMap(r, symSet, funToVarsMap, funToConsMap, varToValMapR, constantValsR, bvOne, maxBVlen, vgBV, formList);

            // Encode and define gr and ge constraint
            SMTLIBBoolVariable gt = SMTLIBBoolVariable.create("gt"+count);
            formList.add(this.addGT(gt, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, maxBVlen));
            nonStrictGTs.add(this.formFactory.buildTheoryAtom(gt));
            SMTLIBBoolVariable ge = SMTLIBBoolVariable.create("ge"+count);
            formList.add(this.addGE(ge, varSet, varToValMapL, constantValsL, varToValMapR, constantValsR, maxBVlen));
            formList.add(this.formFactory.buildTheoryAtom(ge));
        }
        for (Map.Entry<Rule, QActiveCondition> e : R.entrySet()) {
            count++;
            Rule rule = e.getKey();
            TRSTerm l = rule.getLeft();
            TRSTerm r = rule.getRight();
            // Collect values for l
            Map<TRSVariable, List<SMTLIBBVValue>> varToValMapL = new LinkedHashMap<TRSVariable, List<SMTLIBBVValue>>();
            List<SMTLIBBVValue> constantValsL = new LinkedList<SMTLIBBVValue>();
            this.buildVarToValMap(l, symSet, funToVarsMap, funToConsMap, varToValMapL, constantValsL, bvOne, maxBVlen, vgBV, formList);
            // Collect values for r
            Map<TRSVariable, List<SMTLIBBVValue>> varToValMapR = new LinkedHashMap<TRSVariable, List<SMTLIBBVValue>>();
            List<SMTLIBBVValue> constantValsR = new LinkedList<SMTLIBBVValue>();
            this.buildVarToValMap(r, symSet, funToVarsMap, funToConsMap, varToValMapR, constantValsR, bvOne, maxBVlen, vgBV, formList);

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
            Map<TRSVariable, List<SMTLIBBVValue>> varToValMapL = new LinkedHashMap<TRSVariable, List<SMTLIBBVValue>>();
            List<SMTLIBBVValue> constantValsL = new LinkedList<SMTLIBBVValue>();
            this.buildVarToValMap(l, symSet, funToVarsMap, funToConsMap, varToValMapL, constantValsL, bvOne, maxBVlen, vgBV, formList);
            // Collect values for r
            Map<TRSVariable, List<SMTLIBBVValue>> varToValMapR = new LinkedHashMap<TRSVariable, List<SMTLIBBVValue>>();
            List<SMTLIBBVValue> constantValsR = new LinkedList<SMTLIBBVValue>();
            this.buildVarToValMap(r, symSet, funToVarsMap, funToConsMap, varToValMapR, constantValsR, bvOne, maxBVlen, vgBV, formList);

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

        Map<FunctionSymbol, BigInteger> weightMap = new LinkedHashMap<FunctionSymbol, BigInteger>();
        Map<FunctionSymbol, int[]> paramMap = new LinkedHashMap<FunctionSymbol, int[]>();
        for (FunctionSymbol sym : symSet) {
            int arity = sym.getArity();
            SMTLIBBVVariable v = (SMTLIBBVVariable)funToConsMap.get(sym);
            BigInteger weight = BigInteger.valueOf(v.getResultAsUnsignedInteger());
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
