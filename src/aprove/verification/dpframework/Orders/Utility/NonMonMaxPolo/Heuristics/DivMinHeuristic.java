package aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo.Heuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Fine-tuned to tackle the div-system from revision 1.57 of the paper
 * (among the other systems from the paper).
 *
 * Neg coeffs ok if symbol is defined and occurs in rhs of a DP and is
 * not (the only def. symbol and of arity 2, i.e., "app"-like) or
 * if symbol is a head symbol in P (aka "tuple symbol") and lhs of
 * one of these pairs is embedded in rhs. Moreover, symbol must have
 * arity >= 2.
 *
 * Neg consts ok if symbol is destructor (e.g., p(s(x)) -> x removes
 *  context s(.) from x, hence we call p a destructor).
 *
 * Allows max(x_i, x_j) in the interpretation of f if:
 * f is not the only def. symbol and of arity 2, i.e., "app"-like, and
 * There exist rules l_1 -> r_1, l_2 -> r_2 \in R \cup P such that
 * - r_1 and r_2 are variables
 * - l_1 is a superterm of f(s_1, ..., s_n), s_i is r_1
 * - l_2 is a superterm of f(t_1, ..., t_n), t_j is r_2
 * - i != j
 *
 * Allows min(x_i, x_j) in the interpretation of f if:
 * f is not the only def. symbol and of arity 2, i.e., "app"-like, and
 * There exist rules l_1 -> r_1, l_2 -> r_2 \in R \cup P such that
 * - l_1 is a superterm of f(s_1, ..., s_n), s_i is r_1
 * - l_2 is a superterm of f(t_1, ..., t_n), t_j is r_2
 * - i != j
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class DivMinHeuristic {//implements NonMonInterHeuristic {

    private Cand1MMInterHeuristic mmHeuristic;

    private Set<? extends GeneralizedRule> R;
    private Set<? extends GeneralizedRule> P;
    private Set<FunctionSymbol> destructors;
    private Set<FunctionSymbol> defSyms;

    // for a function symbol f, save below which args
    // we have seen some rhs in some corresponding lhs
    private Map<FunctionSymbol, boolean[]> superArgPositionsMax;
    private Map<FunctionSymbol, boolean[]> superArgPositionsMin;

    public DivMinHeuristic() {

        this.resetSuperArgsPositions();
    }

    public boolean allowMax(FunctionSymbol f, int i, int j) {
        if (i == j || i < 0 || j < 0 || i >= f.getArity() || j >= f.getArity()) {
            return false;
        }
        if (f.getArity() == 2 && this.defSyms.size() == 1 && this.defSyms.contains(f)) {
            // beware of applicative symbol
            return false;
        }
        boolean[] allowedArgsForF = this.superArgPositionsMax.get(f);
        return allowedArgsForF[i] && allowedArgsForF[j];
    }

    public boolean allowMin(FunctionSymbol f, int i, int j) {
        if (i == j || i < 0 || j < 0 || i >= f.getArity() || j >= f.getArity()) {
            return false;
        }
        if (f.getArity() == 2 && this.defSyms.size() == 1 && this.defSyms.contains(f)) {
            // beware of applicative symbol
            return false;
        }
        boolean[] allowedArgsForF = this.superArgPositionsMin.get(f);
        return allowedArgsForF[i] && allowedArgsForF[j];
    }

    public boolean allowNegCoeff(FunctionSymbol f) {
        if (f.getArity() < 2) {
            return false;
        }
        if (this.defSyms.contains(f)) {
            if (this.defSyms.size() != 1) { // avoid applicative!
                Set<FunctionSymbol> fSyms = new HashSet<FunctionSymbol>();
                for (GeneralizedRule pRule : this.P) {
                    TRSTerm t = pRule.getRight();
                    t.collectFunctionSymbols(fSyms);
                    if (fSyms.contains(f)) {
                        return true;
                    }
                }
            }
        }
        else {
            for (GeneralizedRule pRule : this.P) {
                if (f.equals(pRule.getRootSymbol())) {
                    Constraint<TRSTerm> rGEl = Constraint.create(pRule.getRight(),
                            pRule.getLeft(), OrderRelation.GR);
                    if (EMB.theEMB.solves(rGEl)) {
                        return true;
                    }
                }
            }

        }
        return false;
    }

    public boolean allowNegCoeff(FunctionSymbol f, int i) {
        return this.allowNegCoeff(f);
    }

    public boolean allowNegConst(FunctionSymbol f) {
        return this.destructors.contains(f);
    }

    public Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f) {
        int arity = f.getArity();
        if (arity < 2 || (arity == 2 && this.defSyms.size() == 1 && this.defSyms.contains(f))) {
            return java.util.Collections.emptySet();
        }
        List<Pair<Integer, Integer>> result = new ArrayList<Pair<Integer, Integer>>();
        boolean[] allowedArgsForF = this.superArgPositionsMax.get(f);
        if (allowedArgsForF != null) {
            for (int i = 0; i < arity; ++i) {
                if (allowedArgsForF[i]) {
                    for (int j = i + 1; j < arity; ++j) {
                        if (allowedArgsForF[j]) {
                            Pair<Integer, Integer> ij = new Pair<Integer, Integer>(i, j);
                            result.add(ij);
                        }
                    }
                }
            }
        }
        return result;
    }

    public Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f) {
        int arity = f.getArity();
        if (arity < 2 || (arity == 2 && this.defSyms.size() == 1 && this.defSyms.contains(f))) {
            return java.util.Collections.emptySet();
        }
        List<Pair<Integer, Integer>> result = new ArrayList<Pair<Integer, Integer>>();
        boolean[] allowedArgsForF = this.superArgPositionsMin.get(f);
        if (allowedArgsForF != null) {
            for (int i = 0; i < arity; ++i) {
                if (allowedArgsForF[i]) {
                    for (int j = i + 1; j < arity; ++j) {
                        if (allowedArgsForF[j]) {
                            Pair<Integer, Integer> ij = new Pair<Integer, Integer>(i, j);
                            result.add(ij);
                        }
                    }
                }
            }
        }
        return result;
    }

    public void setP(Set<? extends GeneralizedRule> p) {
        if (this.P == null) {
            this.addNewDataForMaxMin(p);
        }
        else {
            this.resetSuperArgsPositions();
            this.addNewDataForMaxMin(p);
            if (this.R != null) {
                this.addNewDataForMaxMin(this.R);
            }
        }
        this.P = p;
    }

    public void setR(Set<? extends GeneralizedRule> r) {
        if (this.R == null) {
            this.addNewDataForMaxMin(r);
        }
        else {
            this.resetSuperArgsPositions();
            this.addNewDataForMaxMin(r);
            if (this.P != null) {
                this.addNewDataForMaxMin(this.P);
            }
        }
        this.R = r;
        this.initDestructors();
        this.initDefSyms();
    }

    private void resetSuperArgsPositions() {
        this.superArgPositionsMax = new HashMap<FunctionSymbol, boolean[]>();
        this.superArgPositionsMin = new HashMap<FunctionSymbol, boolean[]>();
    }


    private void addNewDataForMaxMin(Collection<? extends GeneralizedRule> rules) {
        for (GeneralizedRule rule : rules) {
            TRSFunctionApplication l = rule.getLeft();
            Collection<Pair<Position, TRSTerm>> lPosWithSubterms = l.getPositionsWithSubTerms();
            TRSTerm r = rule.getRight();

            for (Pair<Position, TRSTerm> lPosWithSubterm : lPosWithSubterms) {
                TRSTerm subterm = lPosWithSubterm.y;
                Position pos = lPosWithSubterm.x;
                if (subterm.equals(r) && ! pos.isEmptyPosition()) {
                    // Got one! Now save the info for the function symbol
                    // directly above.
                    int j = pos.lastIndex();
                    pos = pos.shorten(1);
                    // every non-leaf of a term is a FunctionApplication,
                    // so the following cast should be safe
                    TRSFunctionApplication gApp = (TRSFunctionApplication) l.getSubterm(pos);
                    FunctionSymbol g = gApp.getRootSymbol();
                    if (r.isVariable()) {
                        this.putMaxArg(g, j);
                    }
                    this.putMinArg(g, j);
                }
            }
        }
    }

    private void initDefSyms() {
        this.defSyms = CollectionUtils.getRootSymbols(this.R);
    }

    private void putMaxArg(FunctionSymbol f, int i) {
        boolean[] positions = this.superArgPositionsMax.get(f);
        if (positions == null) {
            positions = new boolean[f.getArity()];
            Arrays.fill(positions, false);
        }
        positions[i] = true;
        this.superArgPositionsMax.put(f, positions);
    }

    private void putMinArg(FunctionSymbol f, int i) {
        boolean[] positions = this.superArgPositionsMin.get(f);
        if (positions == null) {
            positions = new boolean[f.getArity()];
            Arrays.fill(positions, false);
        }
        positions[i] = true;
        this.superArgPositionsMin.put(f, positions);
    }

    private void initDestructors() {
        // reset possibly invalid computed values
        this.destructors = new LinkedHashSet<FunctionSymbol>();
        for (GeneralizedRule rule : this.R) {
            TRSFunctionApplication lhs = rule.getLeft();
            FunctionSymbol f = lhs.getRootSymbol();
            if (f.getArity() == 1) {
                TRSTerm rhs = rule.getRight();
                if (lhs.hasProperSubterm(rhs)) {
                    this.destructors.add(f);
                }
            }
        }
    }
}
