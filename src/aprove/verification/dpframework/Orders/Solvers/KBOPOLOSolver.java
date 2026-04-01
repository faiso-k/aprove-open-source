package aprove.verification.dpframework.Orders.Solvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
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
 * Solver for the polynomial ordering from the Knuth-Bendix order
 * Only allows a weight for every function symbol, but can be
 * used with SMT solving!
 *
 * @author Andreas Kelle-Emden
 */
public class KBOPOLOSolver implements AbortableConstraintSolver<TRSTerm> {

    private SMTEngine smtChecker = null;

    private static SMTLIBIntConstant INTZERO = SMTLIBIntConstant.create(BigInteger.ZERO);

    public KBOPOLOSolver(final SMTEngine smtChecker) {
        this.smtChecker = smtChecker;
    }

    public void setSMTChecker(final SMTEngine smtChecker) {
        this.smtChecker = smtChecker;
    }

    private int countvar(final TRSTerm t, final TRSVariable var) {
        if (t instanceof TRSVariable) {
            if (t.equals(var)) {
                return 1;
            }
        } else {
            final FunctionSymbol sym = ((TRSFunctionApplication) t).getRootSymbol();
            final int arity = sym.getArity();
            int res = 0;
            for (int i = 0; i < arity; i++) {
                res += this.countvar(((TRSFunctionApplication) t).getArgument(i), var);
            }
            return res;
        }
        return 0;
    }

    private boolean checkApplicable(final TRSTerm l, final TRSTerm r) {
        final Set<TRSVariable> varSet = r.getVariables();
        for (final TRSVariable v : varSet) {
            if (this.countvar(l, v) < this.countvar(r, v)) {
                return false;
            }
        }
        return true;
    }

    // Recursively build the weight of a given term t
    private SMTLIBIntValue getWeight(final TRSTerm t, final Map<FunctionSymbol, SMTLIBIntVariable> funToWeightMap) {
        if (t instanceof TRSVariable) {
            return KBOPOLOSolver.INTZERO;
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) t;
            final FunctionSymbol sym = fa.getRootSymbol();
            final SMTLIBIntVariable w = funToWeightMap.get(sym);
            final int arity = sym.getArity();
            if (arity == 0) {
                return w;
            } else {
                final List<SMTLIBIntValue> plusList = new ArrayList<SMTLIBIntValue>(arity);
                plusList.add(w);
                for (int i = 0; i < arity; i++) {
                    plusList.add(this.getWeight(fa.getArgument(i), funToWeightMap));
                }
                return SMTLIBIntPlus.create(plusList);
            }
        }
    }

    // Encode GREATER EQUAL
    private Formula<SMTLIBTheoryAtom> encodeGE(final TRSTerm l,
        final TRSTerm r,
        final SMTLIBBoolVariable name,
        final Map<FunctionSymbol, SMTLIBIntVariable> funToWeightMap,
        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory) {
        if (l.equals(r)) {
            return formFactory.buildIff(formFactory.buildTheoryAtom(name),
                formFactory.buildTheoryAtom(SMTLIBBoolTrue.create()));
        } else {
            // Get weight string for the terms
            final SMTLIBIntValue valL = this.getWeight(l, funToWeightMap);
            final SMTLIBIntValue valR = this.getWeight(r, funToWeightMap);
            // KBO1: w(l) > w(r)
            final SMTLIBIntGE ge = SMTLIBIntGE.create(valL, valR);
            return formFactory.buildIff(formFactory.buildTheoryAtom(name), formFactory.buildTheoryAtom(ge));
        }
    }

    // Encode GREATER THEN
    private Formula<SMTLIBTheoryAtom> encodeGR(final TRSTerm l,
        final TRSTerm r,
        final SMTLIBBoolVariable name,
        final Map<FunctionSymbol, SMTLIBIntVariable> funToWeightMap,
        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory) {
        // Get weight string for the terms
        final SMTLIBIntValue valL = this.getWeight(l, funToWeightMap);
        final SMTLIBIntValue valR = this.getWeight(r, funToWeightMap);
        // KBO1: w(l) > w(r)
        final SMTLIBIntGT gr = SMTLIBIntGT.create(valL, valR);
        return formFactory.buildIff(formFactory.buildTheoryAtom(name), formFactory.buildTheoryAtom(gr));
    }

    @Override
    public final POLO solve(final Collection<Constraint<TRSTerm>> constraints, final Abortion aborter)
            throws AbortionException {
        return this.solve(constraints, null, aborter);
    }

    public POLO solve(Collection<Constraint<TRSTerm>> cons, Set<? extends GeneralizedRule> nonStrict, final Abortion aborter)
            throws AbortionException {

        final AbstractCircuitFactory<SMTLIBTheoryAtom> formFactory = new FullSharingFlatteningFactory<>();

        if (cons == null) {
            cons = new LinkedHashSet<Constraint<TRSTerm>>();
        }
        if (nonStrict == null) {
            nonStrict = new LinkedHashSet<>();
        }
        final Collection<Constraint<TRSTerm>> cs = new LinkedHashSet<>(cons);

        for (final GeneralizedRule rule : nonStrict) {
            cs.add(Constraint.fromRule(rule, OrderRelation.GE));
        }

        // Check rules for applicability
        boolean isApplicable = true;
        for (final Constraint<TRSTerm> c : cs) {
            if (!this.checkApplicable(c.getLeft(), c.getRight())) {
                isApplicable = false;
            }
        }
        if (!isApplicable) {
            return null;
        }

        // Check function symbols for special characters
        final Set<FunctionSymbol> symSet = Constraint.getFunctionSymbols(cs);
        final Pair<Map<FunctionSymbol, String>, Map<String, FunctionSymbol>> mapPair =
            SMTUtility.getYICESSymNameMap(symSet);
        final Map<FunctionSymbol, String> symNameMap = mapPair.x;
        final Map<String, FunctionSymbol> retrMap = mapPair.y;

        final Map<FunctionSymbol, SMTLIBIntVariable> funToVarMap = new LinkedHashMap<>();
        final Map<SMTLIBIntVariable, FunctionSymbol> varToFunMap = new LinkedHashMap<>();
        for (final Map.Entry<FunctionSymbol, String> e : mapPair.x.entrySet()) {
            final SMTLIBIntVariable var = SMTLIBIntVariable.create("wf" + e.getValue());
            funToVarMap.put(e.getKey(), var);
            varToFunMap.put(var, e.getKey());
        }

        final List<Formula<SMTLIBTheoryAtom>> forms = new LinkedList<>();

        // Weights must be >= 0
        for (final FunctionSymbol sym : symSet) {
            final Formula<SMTLIBTheoryAtom> form =
                formFactory.buildTheoryAtom(SMTLIBIntGE.create(funToVarMap.get(sym), KBOPOLOSolver.INTZERO));
            forms.add(form);
        }

        final Map<String, SMTLIBBoolVariable> nameToVarMap = new LinkedHashMap<>();
        // Encode KBO
        int count = 0;
        for (final GeneralizedRule rule : nonStrict) {
            aborter.checkAbortion();
            count++;
            final TRSTerm l = rule.getLeft();
            final TRSTerm r = rule.getRight();
            String countString = "gr" + count;
            final SMTLIBBoolVariable countVarGR = SMTLIBBoolVariable.create(countString);
            forms.add(this.encodeGR(l, r, countVarGR, funToVarMap, formFactory));
            nameToVarMap.put(countString, countVarGR);
            countString = "ge" + count;
            final SMTLIBBoolVariable countVarGE = SMTLIBBoolVariable.create("ge" + count);
            forms.add(this.encodeGE(l, r, countVarGE, funToVarMap, formFactory));
            nameToVarMap.put(countString, countVarGE);
            forms.add(formFactory.buildTheoryAtom(countVarGE));
        }
        for (final Constraint<TRSTerm> c : cons) {
            aborter.checkAbortion();
            count++;
            final TRSTerm l = c.getLeft();
            final TRSTerm r = c.getRight();
            final OrderRelation rel = c.getType();
            if (rel.equals(OrderRelation.GE)) {
                final String countString = "ge" + count;
                final SMTLIBBoolVariable countVarGE = SMTLIBBoolVariable.create("ge" + count);
                forms.add(this.encodeGE(l, r, countVarGE, funToVarMap, formFactory));
                nameToVarMap.put(countString, countVarGE);
                forms.add(formFactory.buildTheoryAtom(countVarGE));
            } else if (rel.equals(OrderRelation.GR)) {
                final String countString = "gr" + count;
                final SMTLIBBoolVariable countVarGR = SMTLIBBoolVariable.create(countString);
                forms.add(this.encodeGR(l, r, countVarGR, funToVarMap, formFactory));
                nameToVarMap.put(countString, countVarGR);
                forms.add(formFactory.buildTheoryAtom(countVarGR));
            } else if (rel.equals(OrderRelation.EQ)) {
                if (!l.equals(r)) {
                    forms.add(formFactory.buildTheoryAtom(SMTLIBBoolFalse.create()));
                }
            } else {
                // Not supported
                return null;
            }
        }

        if (!nonStrict.isEmpty()) {
            // Encode one-greater constraint for RRR and MRR
            count = 0;
            final List<Formula<SMTLIBTheoryAtom>> orList = new LinkedList<>();
            for (final GeneralizedRule rule : nonStrict) {
                count++;
                final String countString = "gr" + count;
                orList.add(formFactory.buildTheoryAtom(nameToVarMap.get(countString)));
            }
            forms.add(formFactory.buildOr(orList));
        }

        // TODO
        //System.err.println(smtInput);

        // Call the SMT checker
        YNM res;
        try {
            res = this.smtChecker.satisfiable(forms, SMTLogic.QF_LIA, aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Solver error: " + e.getErrorMessage());
            res = YNM.MAYBE;
        }

        if (res != YNM.YES) {
            // SMT checker returned UNSAT or something unknown
            return null;
        }

        final Map<FunctionSymbol, BigInteger> weightMap = new LinkedHashMap<>();

        for (final FunctionSymbol sym : symSet) {
            final SMTLIBIntVariable v = funToVarMap.get(sym);
            final BigInteger weight = v.getResultAsBigInteger();
            if (weight != null) {
                weightMap.put(sym, weight);
            }
        }

        // Check if some symbols do not occur in weight map
        for (final FunctionSymbol sym : symSet) {
            if (weightMap.get(sym) == null) {
                weightMap.put(sym, BigInteger.ZERO);
            }
        }

        final POLO solvingOrder = this.buildPOLO(weightMap);

        // Check order
        if (Globals.useAssertions) {
            if (!nonStrict.isEmpty()) {
                boolean hasOneGreater = false;
                for (final GeneralizedRule rule : nonStrict) {
                    if (!solvingOrder.solves(Constraint.fromRule(rule, OrderRelation.GE))) {
                        System.err.println("Non-strict constraint not solved!");
                        System.err.println("Rule:" + rule);
                        System.err.println("Ordering:\n" + solvingOrder);
                        assert false;
                    }
                    if (solvingOrder.solves(Constraint.fromRule(rule, OrderRelation.GR))) {
                        hasOneGreater = true;
                    }
                }
                if (!hasOneGreater) {
                    System.err.println("No rule is oriented strictly!");
                    System.err.println("Ordering:\n" + solvingOrder);
                    System.err.println("The nonstrict rules are:\n" + nonStrict);
                    System.err.println("The constraints are:\n" + cons);
                    //System.err.println("The encoding was:\n" + smtInput);
                    //System.err.println("Yices output:\n" + resMap);
                    assert false;
                }
            }
            for (final Constraint<TRSTerm> c : cons) {
                if (!solvingOrder.solves(c)) {
                    System.err.println("Constraint not solved!");
                    System.err.println("Constraint:" + c);
                    System.err.println("Ordering:\n" + solvingOrder);
                    assert false;
                }
            }
        }

        return solvingOrder;
    }

    /**
     * Transforms a weight map to an "ordinary" POLO with an explicitly
     * underlying interpretation. E.g., for a binary f, f |-> 9 becomes
     * f |-> x_1 + x_2 + 9.
     *
     * @param weightMap - maps function symbols to weights
     * @return a corresponding POLO
     */
    private POLO buildPOLO(final Map<FunctionSymbol, BigInteger> weightMap) {
        final Interpretation inter = Interpretation.create();

        // cache for VarParts to improve construction of polynomials
        final List<IndefinitePart> varParts = new ArrayList<IndefinitePart>();

        for (final Map.Entry<FunctionSymbol, BigInteger> fToWeight : weightMap.entrySet()) {

            final FunctionSymbol f = fToWeight.getKey();
            final int arity = f.getArity();

            // update cache
            final int size = varParts.size();
            for (int i = size + 1; i <= arity; ++i) {
                // the i-th argument of f (at argument position i-1)
                // is represented by x_i
                final String newVar = Interpretation.VARIABLE_PREFIX + i;
                final IndefinitePart newVarPart = IndefinitePart.create(newVar, 1);
                varParts.add(newVarPart);
            }

            // build map variable -> coeff for poly
            final Map<IndefinitePart, SimplePolynomial> varMonomials =
                new LinkedHashMap<IndefinitePart, SimplePolynomial>(arity + 1);
            for (int i = 0; i < arity; ++i) {
                final IndefinitePart varPart = varParts.get(i);
                varMonomials.put(varPart, SimplePolynomial.ONE);
            }

            // add constant if it is != 0 (VarPolys do not take
            // addends that amount to zero)
            final BigInteger weight = fToWeight.getValue();
            if (weight.signum() != 0) {
                final SimplePolynomial weightPoly = SimplePolynomial.create(weight);
                varMonomials.put(IndefinitePart.ONE, weightPoly);
            }

            // finally assemble the polynomial interpretation for f
            final ImmutableMap<IndefinitePart, SimplePolynomial> immutableVarMonomials =
                ImmutableCreator.create(varMonomials);
            final VarPolynomial fInter = VarPolynomial.create(immutableVarMonomials);
            inter.put(f, fInter);
        }
        final POLO polo = POLO.create(inter);
        return polo;
    }
}
