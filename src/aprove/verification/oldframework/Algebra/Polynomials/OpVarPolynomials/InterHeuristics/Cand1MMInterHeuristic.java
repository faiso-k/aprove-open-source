package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Candidate for becoming the default heuristic.
 *
 * Allows max(x_i, x_j) in the interpretation of f if i != j and:
 *
 * (1)
 * There exist rules l_1 -> r_1, l_2 -> r_2 \in R \cup P such that
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
 * Allows min(x_i, x_j) in the interpretation of f if i != j and:
 *
 * There exist rules l_1 -> r_1, l_2 -> r_2 \in R \cup P such that
 * - r_1 and r_2 are constructor ground terms
 * - l_1 is a superterm of f(s_1, ..., s_n), s_i is r_1
 * - l_2 is a superterm of f(t_1, ..., t_n), t_j is r_2
 *
 * @author fuhs
 * @version $Id$
 */
public class Cand1MMInterHeuristic implements MMInterHeuristic {

    // for a function symbol f, save below which args
    // we have seen some rhs in some corresponding lhs
    protected Map<FunctionSymbol, boolean[]> superArgPositionsMax;
    protected Map<FunctionSymbol, boolean[]> superArgPositionsMin;
    protected Set<FunctionSymbol> defSyms;

    public Cand1MMInterHeuristic() {
    }

    /*
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
    }*/

    @Override
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

    @Override
    public Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f) {
        int arity = f.getArity();
        if (arity < 2 || (f.getArity() == 2 && this.defSyms.size() == 1 && this.defSyms.contains(f))) {
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

    @Override
    public void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {
        this.defSyms = CollectionUtils.getRootSymbols(r);
        this.resetSuperArgsPositions();
        this.addNewData(r);
        this.addNewData(p);
    }

    private void resetSuperArgsPositions() {
        this.superArgPositionsMax = new HashMap<FunctionSymbol, boolean[]>();
        this.superArgPositionsMin = new HashMap<FunctionSymbol, boolean[]>();
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
                    if (r.isVariable()) {
                        // variable -> max
                        this.putMaxArg(g, j);
                    }
                    else if (r.getVariables().isEmpty() &&
                            java.util.Collections.disjoint(r.getFunctionSymbols(), this.defSyms)) {
                        // constructor ground term

                        // now require that the other arg(s) of the lhs are /non/-ground
                        // -> min
                        int arityOfG = g.getArity();
                        boolean otherArgsNonGround = true;
                        for (int i = 0; i < arityOfG; ++i) {
                            if (i != j && gApp.getArgument(i).getVariables().isEmpty()) {
                                otherArgsNonGround = false;
                            }
                        }

                        if (otherArgsNonGround) {
                            this.putMinArg(g, j);
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


    protected void putMaxArg(FunctionSymbol f, int i) {
        boolean[] positions = this.superArgPositionsMax.get(f);
        if (positions == null) {
            positions = new boolean[f.getArity()];
            Arrays.fill(positions, false);
        }
        positions[i] = true;
        this.superArgPositionsMax.put(f, positions);
    }

    protected void putMinArg(FunctionSymbol f, int i) {
        boolean[] positions = this.superArgPositionsMin.get(f);
        if (positions == null) {
            positions = new boolean[f.getArity()];
            Arrays.fill(positions, false);
        }
        positions[i] = true;
        this.superArgPositionsMin.put(f, positions);
    }

    /**
     * @return the defSyms
     */
    public Set<FunctionSymbol> getDefSyms() {
        return this.defSyms;
    }
}
