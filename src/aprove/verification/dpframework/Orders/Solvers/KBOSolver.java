package aprove.verification.dpframework.Orders.Solvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.KBO.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * KBO Solver according to Korovin, Voronkov 01.
 * Modifications: Handle >= constraints as well (empty tupleineq. are satisfiable for >=).
 * @author  Rene Thiemann
 */

public class KBOSolver implements AbortableConstraintSolver<TRSTerm> {

    private static final KBOSolver THE_SOLVER = new KBOSolver();

    /**
     * Creates an instance of <code>KBOSolver</code>.
     */
    public static KBOSolver create() {
        return KBOSolver.THE_SOLVER;
    }

    /**
     * Checks, whether all constraints can be satisfied by some KBO.
     * @param constraints a set of constraints with types EQ, GE, or GR.
     * @return a solving KBO, if it exists, and otherwise null.
     * @throws AbortionException
     */
    @Override
    public final ExportableOrder<TRSTerm> solve(final Collection<Constraint<TRSTerm>> constraints, final Abortion aborter)
            throws AbortionException {
        final Set<FunctionSymbol> signature = new HashSet<FunctionSymbol>();
        final List<Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, Boolean, Set<TRSVariable>, HomogenousInequality>> RwithM =
            new ArrayList<Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, Boolean, Set<TRSVariable>, HomogenousInequality>>(
                constraints.size());

        // compute constraints and signature
        for (final Constraint<TRSTerm> constraint : constraints) {
            final TRSTerm left = constraint.x;
            final TRSTerm right = constraint.y;
            left.collectFunctionSymbols(signature);
            right.collectFunctionSymbols(signature);
            final OrderRelation rel = constraint.z;
            Boolean strict;
            if (rel == OrderRelation.GE) {
                if (left.equals(right)) {
                    continue;
                }
                strict = Boolean.FALSE;
            } else if (rel == OrderRelation.GR) {
                if (EMB.theEMB.inRelation(left, right)) {
                    continue;
                }
                strict = Boolean.TRUE;
            } else if (rel == OrderRelation.EQ) {
                if (left.equals(right)) {
                    continue;
                } else {
                    return null;
                }
            } else {
                throw new RuntimeException("Unknown Relation type in KBO-Solver: " + rel);
            }
            final ArrayStack<Pair<InfoTerm, InfoTerm>> stack = new ArrayStack<Pair<InfoTerm, InfoTerm>>(5);
            final InfoTerm ileft = new InfoTerm(left);
            final InfoTerm iright = new InfoTerm(right);

            //  fast check on var-condition:
            if (!iright.vars.isSubsetOf(ileft.vars)) {
                return null;
            }
            stack.push(new Pair<InfoTerm, InfoTerm>(ileft, iright));
            RwithM.add(new Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, Boolean, Set<TRSVariable>, HomogenousInequality>(
                stack, strict, new HashSet<TRSVariable>(5), null));
        }

        // check for constant in signature
        boolean gotConstant = false;
        for (final FunctionSymbol f : signature) {
            if (f.getArity() == 0) {
                gotConstant = true;
                break;
            }
        }

        if (!gotConstant) {
            signature.add(FunctionSymbol.create("dummyConstant", 0));
        }

        // create initial D
        final List<FunctionSymbol> signatureList = new ArrayList<FunctionSymbol>(signature);
        final Set<HomogenousInequality> initialInequalities =
            new LinkedHashSet<HomogenousInequality>(signature.size() + 1);

        initialInequalities.add(KBOSolver.getInequalityVar(signatureList.size()));
        for (final FunctionSymbol f : signatureList) {
            if (f.getArity() == 0) {
                initialInequalities.add(KBOSolver.getInequalityConst(f, signatureList));
            } else {
                initialInequalities.add(KBOSolver.getInequalityFSym(f, signatureList));
            }
        }
        final HomogenousInequalitySystem D = new HomogenousInequalitySystem(initialInequalities);

        // and create the remaining start values
        final Poset<FunctionSymbol> precedence = Poset.create(signature);
        final FunctionSymbol leastConstantOfMinimalWeight = null;
        final FunctionSymbol greatestTermOfMinimalWeight = null;
        final boolean uniqueMinimalTerm = false;

        return KBOSolver.solvingOrder(RwithM, D, precedence, leastConstantOfMinimalWeight, greatestTermOfMinimalWeight,
            uniqueMinimalTerm, signatureList, aborter);
    }

    /**
     * The method to compute a solution according to Korovin, Voronkov with
     * some minor modifications for GE-constraints.
     */
    private final static ExportableOrder<TRSTerm> solvingOrder(
    // the set of constraints (R) with attached set of minimal variables (M) and the
    // inequality for step M3. If the ineq. is non-null, then this means that
    // the steps M1-M3 have already be done with the first entry in the ArrayStack.
    // The Boolean encodes strict/non-strict.
    final List<Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, Boolean, Set<TRSVariable>, HomogenousInequality>> RwithM,
        final HomogenousInequalitySystem D,
        final Poset<FunctionSymbol> precedence,
        FunctionSymbol leastConstantOfMinimalWeight, // = L
        FunctionSymbol greatestTermOfMinimalWeight, // = G
        boolean uniqueMinimalTerm, // = U, true = ONE, false = ANY
        final List<FunctionSymbol> signature, // the signature of the initial constraints
        final Abortion aborter) throws AbortionException {

        while (true) {
            aborter.checkAbortion();
            // preprocess
            Iterator<Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, Boolean, Set<TRSVariable>, HomogenousInequality>> Riter =
                RwithM.iterator();
            while (Riter.hasNext()) {

                final Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, Boolean, Set<TRSVariable>, HomogenousInequality> tupleIneqWithFlagAndM =
                    Riter.next();

                // if we have already processed this with M1-M3, then we do not need to do it again!
                if (tupleIneqWithFlagAndM.z == null) {
                    final ArrayStack<Pair<InfoTerm, InfoTerm>> tupleIneq = tupleIneqWithFlagAndM.w;
                    KBOSolver.removeFirstEquals(tupleIneq);
                    if (tupleIneq.isEmpty()) {
                        if (tupleIneqWithFlagAndM.x) { // strict case, then fail
                            return null;
                        } else { // non-strict, so we are done
                            Riter.remove();
                        }
                    } else {
                        // do M1, M2, M3
                        final Pair<InfoTerm, InfoTerm> tt = tupleIneq.peek();
                        final InfoTerm ileft = tt.x;
                        final InfoTerm iright = tt.y;

                        final MultiSet<TRSVariable> leftVars = ileft.vars;
                        final MultiSet<TRSVariable> rightVars = iright.vars;
                        final Set<TRSVariable> M = tupleIneqWithFlagAndM.y;

                        // M1
                        for (final Map.Entry<TRSVariable, Integer> leftVar : leftVars.entrySet()) {
                            final TRSVariable v = leftVar.getKey();
                            final int countRight = rightVars.frequency(v);
                            final int countLeft = leftVar.getValue();
                            if (countLeft > countRight) {
                                M.add(v);
                            }
                        }

                        // M2
                        for (final Map.Entry<TRSVariable, Integer> rightVar : rightVars.entrySet()) {
                            final TRSVariable v = rightVar.getKey();
                            final int countLeft = leftVars.frequency(v);
                            final int countRight = rightVar.getValue();
                            if (countLeft < countRight && !M.contains(v)) {
                                return null;
                            }
                        }

                        // M3
                        tupleIneqWithFlagAndM.z = KBOSolver.buildInequality(ileft, iright, signature);
                        D.add(tupleIneqWithFlagAndM.z);

                    }
                }
            }

            // okay, perform new consistency check
            if (!D.hasSolution()) {
                return null;
            }

            final Set<HomogenousInequality> Dequal = D.getDegenerateSubSystem();
            if (Dequal.contains(KBOSolver.getInequalityVar(signature.size()))) {
                // D has no non-trivial solution, abort
                return null;
            }

            // now check the special cases M4-M8 (same weights)
            boolean gotSomeDequal = false;
            if (!Dequal.isEmpty()) {
                Riter = RwithM.iterator();
                while (Riter.hasNext()) {

                    final Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, Boolean, Set<TRSVariable>, HomogenousInequality> tupleIneqWithFlagAndM =
                        Riter.next();
                    final HomogenousInequality ineq = tupleIneqWithFlagAndM.z;
                    if (Globals.useAssertions) {
                        assert (ineq != null);
                    }
                    if (Dequal.contains(ineq)) {
                        gotSomeDequal = true;

                        tupleIneqWithFlagAndM.z = null; // we will create something new, so cannot reuse the old inequality.

                        final ArrayStack<Pair<InfoTerm, InfoTerm>> tupleIneq = tupleIneqWithFlagAndM.w;
                        final boolean strict = tupleIneqWithFlagAndM.x;
                        final Pair<InfoTerm, InfoTerm> tt = tupleIneq.pop();
                        final InfoTerm ileft = tt.x;
                        final InfoTerm iright = tt.y;

                        final TRSTerm left = ileft.term;
                        final TRSTerm right = iright.term;

                        final boolean varLeft = left.isVariable();
                        final boolean varRight = right.isVariable();

                        // M4 and M5
                        if (!varRight && !varLeft) {
                            final TRSFunctionApplication fLeft = (TRSFunctionApplication) left;
                            final TRSFunctionApplication gRight = (TRSFunctionApplication) right;
                            final FunctionSymbol f = fLeft.getRootSymbol();
                            final FunctionSymbol g = gRight.getRootSymbol();
                            if (f.equals(g)) {
                                // M5
                                KBOSolver.insertArguments(tupleIneq, ileft, iright);
                            } else {
                                // M4
                                try {
                                    precedence.setGreater(f, g);
                                    Riter.remove();
                                } catch (final OrderedSetException e) {
                                    return null;
                                }
                            }
                        } else if (varLeft && varRight) {
                            // M6
                            uniqueMinimalTerm = true;
                        } else if (varLeft && !varRight) {
                            // M7
                            final FunctionSymbol f = ((TRSFunctionApplication) right).getRootSymbol();
                            if (f.getArity() == 0
                                && (leastConstantOfMinimalWeight == null || leastConstantOfMinimalWeight.equals(f))) {
                                leastConstantOfMinimalWeight = f;
                                if (strict) {
                                    return null;
                                }
                            } else {
                                return null;
                            }
                        } else {
                            // M8
                            final TRSVariable v = (TRSVariable) right;
                            if (Globals.useAssertions) {
                                assert (!varLeft && varRight);
                            }
                            if (ileft.vars.contains(v)) {
                                Riter.remove();
                            } else {
                                final FunctionSymbol f = ((TRSFunctionApplication) left).getRootSymbol();
                                if (f.getArity() == 0
                                    && (greatestTermOfMinimalWeight == null || greatestTermOfMinimalWeight.equals(f))) {
                                    greatestTermOfMinimalWeight = f;
                                    KBOSolver.replaceVariables(tupleIneq, v, ileft);
                                } else {
                                    return null;
                                }
                            }
                        }
                    }
                }
            }

            if (gotSomeDequal) {
                continue; // Back to preprocess
            }

            // TERMINATE:
            int gotWc_We_in_Dequal = 0;
            final Collection<FunctionSymbol> constants = new ArrayList<FunctionSymbol>();
            try {
                // T1 & T2
                final boolean checkLeast = leastConstantOfMinimalWeight != null;
                final boolean checkGreatest = greatestTermOfMinimalWeight != null;
                for (final FunctionSymbol f : signature) {
                    final int n = f.getArity();
                    if (n == 0) {
                        final boolean inDEqual = Dequal.contains(KBOSolver.getInequalityConst(f, signature));
                        if (inDEqual) {
                            gotWc_We_in_Dequal++;
                        } else {
                            if (gotWc_We_in_Dequal == 0) {
                                constants.add(f);
                            }
                        }

                        // T1
                        final boolean cL = checkLeast && !f.equals(leastConstantOfMinimalWeight);
                        final boolean cG = checkGreatest && !f.equals(greatestTermOfMinimalWeight);
                        if (cL || cG) {
                            if (inDEqual) {
                                if (cL) {
                                    precedence.setGreater(f, leastConstantOfMinimalWeight);
                                }
                                if (cG) {
                                    precedence.setGreater(greatestTermOfMinimalWeight, f);
                                }
                            }
                        }
                    } else if (n == 1) {
                        // T2
                        if (Dequal.contains(KBOSolver.getInequalityFSym(f, signature))) {
                            if (uniqueMinimalTerm || checkGreatest) {
                                return null;
                            }
                            for (final FunctionSymbol g : signature) {
                                if (!f.equals(g)) {
                                    precedence.setGreater(f, g);
                                }
                            }
                        }
                    }
                }
            } catch (final OrderedSetException e) {
                return null;
            }

            // T4
            if (uniqueMinimalTerm && gotWc_We_in_Dequal > 1) {
                return null;
            }

            // T3
            if (gotWc_We_in_Dequal == 0) {
                for (final FunctionSymbol c : constants) {
                    final HomogenousInequalitySystem Dcopy = D.deepcopy();
                    Dcopy.add(KBOSolver.getInequalityConstCompl(c, signature));
                    if (Dcopy.hasSolution()) {
                        final ExportableOrder<TRSTerm> maybeSolution =
                            KBOSolver.solvingOrder(KBOSolver.copyRWithM(RwithM), Dcopy, precedence.deepcopy(),
                                leastConstantOfMinimalWeight, greatestTermOfMinimalWeight, uniqueMinimalTerm,
                                signature, aborter);
                        if (maybeSolution != null) {
                            return maybeSolution;
                        }
                    }
                }
                return null;
            }

            // T5
            final Map<FunctionSymbol, BigInteger> weightMap =
                KBOSolver.buildWeightMap(D.getMinimalSolution(), signature);
            return new KBO(precedence, weightMap);
        }
    }

    private static <U, V> List<Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, U, Set<TRSVariable>, V>> copyRWithM(final List<Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, U, Set<TRSVariable>, V>> RWithM) {
        final List<Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, U, Set<TRSVariable>, V>> res =
            new ArrayList<Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, U, Set<TRSVariable>, V>>(RWithM.size());
        for (final Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, U, Set<TRSVariable>, V> entry : RWithM) {
            res.add(new Quadruple<ArrayStack<Pair<InfoTerm, InfoTerm>>, U, Set<TRSVariable>, V>(
                new ArrayStack<Pair<InfoTerm, InfoTerm>>(entry.w), entry.x, new HashSet<TRSVariable>(entry.y), entry.z));
        }
        return res;
    }

    /**
     * Builds an inequality of two terms.
     */
    private static HomogenousInequality buildInequality(final InfoTerm left,
        final InfoTerm right,
        final List<FunctionSymbol> signature) {
        final List<BigInteger> coeff = new ArrayList<BigInteger>(signature.size() + 1);
        final MultiSet<FunctionSymbol> fsLhs = left.fs;
        final MultiSet<FunctionSymbol> fsRhs = right.fs;

        for (final FunctionSymbol f : signature) {
            final BigInteger fsymNumberCoeff = BigInteger.valueOf(fsLhs.frequency(f) - fsRhs.frequency(f));
            coeff.add(fsymNumberCoeff);
        }
        final BigInteger varNumbersCoeff = BigInteger.valueOf(left.vars.multiSize() - right.vars.multiSize());
        coeff.add(varNumbersCoeff);
        return HomogenousInequality.create(coeff);
    }

    /**
     * Builds the weight map of the minimal solution of the inequality system.
     */
    private static Map<FunctionSymbol, BigInteger> buildWeightMap(final List<BigInteger> solution,
        final List<FunctionSymbol> signature) {
        final Map<FunctionSymbol, BigInteger> res = new HashMap<FunctionSymbol, BigInteger>(signature.size());
        final Iterator<BigInteger> solIter = solution.iterator();
        for (final FunctionSymbol f : signature) {
            final BigInteger weight = solIter.next();
            res.put(f, weight);
        }

        // minimal weight = solIter.next();

        return res;
    }

    /**
     * Returns an inequality of form: w_e >= 0
     * @return inequality w_e >= 0
     */
    private static HomogenousInequality getInequalityVar(final int sizeSignature) {
        final List<BigInteger> coeff = new ArrayList<BigInteger>(sizeSignature + 1);
        final BigInteger ZERO = BigInteger.ZERO;
        for (int i = 0; i < sizeSignature; i++) {
            coeff.add(ZERO);
        }
        coeff.add(BigInteger.ONE);
        return HomogenousInequality.create(coeff);
    }

    /**
     * Returns an inequality of form: w_c - w_e >= 0
     * @param c the constant, the inequality should be build of
     * @return inequality w_c - w_e >= 0
     */
    private static HomogenousInequality getInequalityConst(final FunctionSymbol c, final List<FunctionSymbol> signature) {
        final List<BigInteger> coeff = new ArrayList<BigInteger>(signature.size() + 1);
        final BigInteger ZERO = BigInteger.ZERO;
        for (final FunctionSymbol f : signature) {
            if (f.equals(c)) {
                coeff.add(BigInteger.ONE);
            } else {
                coeff.add(ZERO);
            }
        }
        coeff.add(BigInteger.valueOf(-1));
        return HomogenousInequality.create(coeff);
    }

    /**
     * Returns an inequality of form: w_e - w_c >= 0
     * @param c the constant, the inequality should be build of
     * @return inequality w_e - w_c >= 0
     */
    private static HomogenousInequality getInequalityConstCompl(final FunctionSymbol c,
        final List<FunctionSymbol> signature) {
        final List<BigInteger> coeff = new ArrayList<BigInteger>(signature.size() + 1);
        final BigInteger ZERO = BigInteger.ZERO;
        for (final FunctionSymbol f : signature) {
            if (f.equals(c)) {
                coeff.add(BigInteger.valueOf(-1));
            } else {
                coeff.add(ZERO);
            }
        }
        coeff.add(BigInteger.ONE);
        return HomogenousInequality.create(coeff);
    }

    /**
     * Returns an inequality of form: w_fsym >= 0
     * @param fsym the function symbol, the inequality should be build of
     * @return inequality w_fsym >= 0
     */
    private static HomogenousInequality getInequalityFSym(final FunctionSymbol g, final List<FunctionSymbol> signature) {
        final List<BigInteger> coeff = new ArrayList<BigInteger>(signature.size() + 1);
        final BigInteger ZERO = BigInteger.ZERO;
        for (final FunctionSymbol f : signature) {
            if (f.equals(g)) {
                coeff.add(BigInteger.ONE);
            } else {
                coeff.add(ZERO);
            }
        }
        coeff.add(ZERO);
        return HomogenousInequality.create(coeff);
    }

    /**
     * substitues v/t in all terms in the list
     * @param list
     * @param v
     * @param t
     */
    private static final void replaceVariables(final List<Pair<InfoTerm, InfoTerm>> list,
        final TRSVariable v,
        final InfoTerm t) {
        final ListIterator<Pair<InfoTerm, InfoTerm>> i = list.listIterator();
        while (i.hasNext()) {
            Pair<InfoTerm, InfoTerm> pair = i.next();
            pair = new Pair<InfoTerm, InfoTerm>(pair.x.replaceVariable(v, t), pair.y.replaceVariable(v, t));
            i.set(pair);
        }
    }

    /**
     * removes all pairs from the beginning of the list, until there
     * is no pair any more, or the first pair is different.
     * @param list
     */
    private static final <X> void removeFirstEquals(final List<Pair<X, X>> list) {
        final Iterator<Pair<X, X>> i = list.iterator();
        while (i.hasNext()) {
            final Pair<X, X> pair = i.next();
            if (pair.x.equals(pair.y)) {
                i.remove();
            } else {
                break;
            }
        }
    }

    /**
     * inserts (t_1,s_1),..,(t_n,s_n) in front of the list, such that (t_1,s_1) will be returned first by the iterator
     * of the list afterwards.
     * @param list
     * @param left has to be f(t_1,..,t_n)
     * @param right has to be f(s_1,..,s_n)
     */
    private static final void insertArguments(final ArrayStack<Pair<InfoTerm, InfoTerm>> list,
        final InfoTerm left,
        final InfoTerm right) {
        final List<InfoTerm> l = left.args;
        final List<InfoTerm> r = right.args;
        int i = l.size();
        list.ensureCapacity(list.size() + i);
        while (i > 0) {
            i--;
            list.push(new Pair<InfoTerm, InfoTerm>(l.get(i), r.get(i)));
        }
    }

    private static final MultiSet<FunctionSymbol> EMPTY_SET = new HashMultiSet<FunctionSymbol>(0);

    /**
     * a InfoTerm stores things as number of vars, number of fs, ...
     * even for its subterms. Used for speedup in calculation.
     *
     * @author thiemann
     *
     */
    private static class InfoTerm {

        public final TRSTerm term;
        public final MultiSet<TRSVariable> vars;
        public final MultiSet<FunctionSymbol> fs;
        public final List<InfoTerm> args;

        public InfoTerm(final TRSTerm t) {
            this.term = t;
            if (t.isVariable()) {
                this.vars = new HashMultiSet<TRSVariable>(1);
                this.vars.add((TRSVariable) t, 1);
                this.fs = KBOSolver.EMPTY_SET;
                this.args = null;
            } else {
                final TRSFunctionApplication ft = (TRSFunctionApplication) t;
                final FunctionSymbol f = ft.getRootSymbol();
                final int n = f.getArity();
                this.vars = new HashMultiSet<TRSVariable>(n);
                this.fs = new HashMultiSet<FunctionSymbol>(n * 2 + 1);
                this.fs.add(f, 1);
                this.args = new ArrayList<InfoTerm>(n);
                for (final TRSTerm arg : ft.getArguments()) {
                    final InfoTerm infoArg = new InfoTerm(arg);
                    this.args.add(infoArg);
                    this.vars.addAll(infoArg.vars);
                    this.fs.addAll(infoArg.fs);
                }
            }
        }

        private InfoTerm(final TRSFunctionApplication t, final MultiSet<TRSVariable> vars, final MultiSet<FunctionSymbol> fs,
                final List<InfoTerm> args) {
            this.term = t;
            this.vars = vars;
            this.fs = fs;
            this.args = args;
        }

        public InfoTerm replaceVariable(final TRSVariable v, final InfoTerm t) {
            if (this.vars.contains(v)) {
                if (this.args == null) {
                    // are we a variable
                    return t;
                } else {
                    // or a functionApplication
                    final TRSFunctionApplication fterm = (TRSFunctionApplication) this.term;
                    final FunctionSymbol f = fterm.getRootSymbol();
                    final int n = f.getArity();
                    final List<InfoTerm> newInfos = new ArrayList<InfoTerm>(n);
                    final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(n);
                    final MultiSet<TRSVariable> newVars = new HashMultiSet<TRSVariable>(this.vars);
                    final MultiSet<FunctionSymbol> newFs = new HashMultiSet<FunctionSymbol>(this.fs);
                    for (final InfoTerm argInfo : this.args) {
                        final InfoTerm newArgInfo = argInfo.replaceVariable(v, t);
                        if (argInfo != newArgInfo) {
                            newVars.removeAll(argInfo.vars);
                            newVars.addAll(newArgInfo.vars);
                            newFs.removeAll(argInfo.fs);
                            newFs.addAll(newArgInfo.fs);
                        }
                        newInfos.add(newArgInfo);
                        newArgs.add(newArgInfo.term);
                    }
                    final TRSFunctionApplication newTerm =
                        TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));

                    return new InfoTerm(newTerm, newVars, newFs, newInfos);

                }
            } else {
                return this;
            }
        }

        @Override
        public String toString() {
            return this.term.toString();
        }

        @Override
        public boolean equals(final Object other) {
            if (other == null) {
                return false;
            }
            final InfoTerm info = (InfoTerm) other;
            return this.term.equals(info.term);
        }

        @Override
        public int hashCode() {
            return this.term.hashCode();
        }
    }

}
