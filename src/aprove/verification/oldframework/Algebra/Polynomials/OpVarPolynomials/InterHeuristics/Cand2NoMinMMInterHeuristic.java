package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Candidate for becoming the default heuristic.
 *
 * Allows max(x_i, x_j) in the interpretation of f if i != j,
 * f occurs in some reducible rhs of R, and:
 *
 * (1) There exist rules l_1 -> r_1, l_2 -> r_2 \in R \cup P such that
 * - r_1 and r_2 are variables
 * - l_1 is a superterm of f(s_1, ..., s_n), s_i is r_1
 * - l_2 is a superterm of f(t_1, ..., t_n), t_j is r_2
 *
 * or (2)
 * arity(f) == 2 and there is some rule l -> r in R \cup P with
 *
 *   r = C[ f(..., D[y], ..., E[y], ...) ] for some contexts C, D, E
 *                 ^^^^       ^^^^
 *            i-th pos.       j-th pos.
 *
 * Never allows min(x_i, x_j).
 *
 * @author fuhs
 * @version $Id$
 */
public class Cand2NoMinMMInterHeuristic {//implements MMInterHeuristic {

    private Set<? extends GeneralizedRule> P;
    private Map<Rule, QActiveCondition> R;

    // for a function symbol f, save below which args
    // we have seen some rhs in some corresponding lhs
    private Map<FunctionSymbol, boolean[]> superArgPositionsMax;
    private Set<FunctionSymbol> defSyms;
    private Set<FunctionSymbol> symsInReducibleRhss;

    public Cand2NoMinMMInterHeuristic() {
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
        return false;
    }

    public Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f) {
        int arity = f.getArity();
        if (arity < 2 || (f.getArity() == 2 && this.defSyms.size() == 1 && this.defSyms.contains(f))) {
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
        return java.util.Collections.emptySet();
    }

    public void setP(Set<? extends GeneralizedRule> p) {
        if (this.P == null) {
            this.P = p;
            this.addNewData(p);
        }
        else {
            this.P = p;
            this.resetSuperArgsPositions();
            this.addNewData(p);
            if (this.R != null) {
                this.addNewData(this.R.keySet());
            }
        }
    }

    public void setR(Map<Rule, QActiveCondition> r) {
        if (this.R == null) {
            this.R = r;
            this.gatherSymbolsInReducibleRhss();
            this.addNewData(r.keySet());
        }
        else {
            this.R = r;
            this.resetSuperArgsPositions();
            this.gatherSymbolsInReducibleRhss();
            this.addNewData(r.keySet());
            if (this.P != null) {
                this.addNewData(this.P);
            }
        }
        this.defSyms = CollectionUtils.getRootSymbols(this.R.keySet());
    }

    private void gatherSymbolsInReducibleRhss() {
        this.symsInReducibleRhss = new LinkedHashSet<FunctionSymbol>();
        QTermSet leftOfR = new QTermSet(CollectionUtils.getLeftHandSides(this.R.keySet()));
        for (GeneralizedRule rule : this.R.keySet()) {
            TRSTerm rhs = rule.getRight();
            boolean canBeRewritten = leftOfR.canBeRewritten(rhs);
            if (canBeRewritten) {
                rhs.collectFunctionSymbols(this.symsInReducibleRhss);
            }
        }
    }

    private void resetSuperArgsPositions() {
        this.superArgPositionsMax = new HashMap<FunctionSymbol, boolean[]>();
    }

    private void addNewData(Set<? extends GeneralizedRule> rules) {
        this.addDuplData(rules);
        this.addProjectionData(rules);
    }

    protected void addProjectionData(Collection<? extends GeneralizedRule> rules) {
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

                    // moreover require that g occurs in some rhs of R which is reducible
                    if (this.symsInReducibleRhss.contains(g)) {
                        if (r.isVariable()) {
                            // variable -> max
                            this.putMaxArg(g, j);
                        }
                    }
                }
            }
        }
    }

    private void addDuplData(Collection<? extends GeneralizedRule> rules) {
        for (GeneralizedRule rule : rules) {
            TRSTerm r = rule.getRight();
            Map<TRSVariable, List<Position>> varPositions = r.getVariablePositions();
            for (List<Position> positions : varPositions.values()) {
                final int size = positions.size();
                for (int i1 = 0; i1 < size; ++i1) {
                    Position p1 = positions.get(i1);
                    for (int i2 = i1 + 1; i2 < size; ++i2) {
                        Position p2 = positions.get(i2);
                        Position forkPos = p1.getLongestCommonPrefix(p2);

                        // the following cast is (hopefully) safe because
                        // two different occurrences of a variable in a term
                        // have a longest common prefix position at which
                        // there is a function symbol
                        TRSFunctionApplication fApp = (TRSFunctionApplication) r.getSubterm(forkPos);
                        FunctionSymbol f = fApp.getRootSymbol();

                        // require constructor symbol of arity 2
                        if (f.getArity() == 2 && ! this.defSyms.contains(f)) {
                            // below which args of f did the fork happen?
                            int arg1 = p1.toIntArray()[forkPos.getDepth()];
                            int arg2 = p2.toIntArray()[forkPos.getDepth()];
                            if (Globals.useAssertions) {
                                assert arg1 != arg2;
                                // otherwise forkPos was not the /longest/
                                // common prefix
                            }
                            this.putMaxArg(f, arg1);
                            this.putMaxArg(f, arg2);
                        }
                    }
                }
            }
        }
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
}
