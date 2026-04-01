package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Allows max(x_i, x_j) and min(x_i, x_j) in the interpretation of f
 * if there is some rule l -> r in R \cup P with
 *
 *   r = C[ f(..., D[y], ..., E[y], ...) ] for some contexts C, D, E
 *                 ^^^^       ^^^^
 *            i-th pos.       j-th pos.
 *
 * @author fuhs
 * @version $Id$
 */
public class DuplMMInterHeuristic implements MMInterHeuristic {

    // for a function symbol f, save below which args
    // we have seen some rhs in some corresponding lhs
    private Map<FunctionSymbol, boolean[]> superArgPositionsMax;
    private Map<FunctionSymbol, boolean[]> superArgPositionsMin;

    public DuplMMInterHeuristic() {
        this.resetSuperArgsPositions();
    }

    public boolean allowMax(FunctionSymbol f, int i, int j) {
        if (i == j || i < 0 || j < 0 || i >= f.getArity() || j >= f.getArity()) {
            return false;
        }
        boolean[] allowedArgsForF = this.superArgPositionsMax.get(f);
        return allowedArgsForF[i] && allowedArgsForF[j];
    }

    public boolean allowMin(FunctionSymbol f, int i, int j) {
        if (i == j || i < 0 || j < 0 || i >= f.getArity() || j >= f.getArity()) {
            return false;
        }
        boolean[] allowedArgsForF = this.superArgPositionsMin.get(f);
        return allowedArgsForF[i] && allowedArgsForF[j];
    }


    @Override
    public Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f) {
        int arity = f.getArity();
        if (arity < 2) {
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
        if (arity < 2) {
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
        this.resetSuperArgsPositions();
        this.addNewData(p);
        this.addNewData(r);
    }

    private void resetSuperArgsPositions() {
        this.superArgPositionsMax = new HashMap<FunctionSymbol, boolean[]>();
        this.superArgPositionsMin = new HashMap<FunctionSymbol, boolean[]>();
    }

    private void addNewData(Collection<? extends GeneralizedRule> rules) {
        for (GeneralizedRule rule : rules) {
            TRSTerm r = rule.getRight();
            Map<TRSVariable, List<Position>> varPositions = r.getVariablePositions();
            for (List<Position> positions : varPositions.values()) {
                final int size = positions.size();
                for (int i1 = 0; i1 < size; ++i1) {
                    Position p1 = positions.get(i1);
                    for (int i2 = i1 + 1; i2 < size; ++i2) {
                        Position p2 = positions.get(i2);
                        if (Globals.useAssertions) {
                            assert ! p1.equals(p2);
                        }
                        Position forkPos = p1.getLongestCommonPrefix(p2);

                        // the following cast is (hopefully) safe because
                        // two different occurrences of a variable in a term
                        // have a longest common prefix position at which
                        // there is a function symbol
                        TRSFunctionApplication fApp = (TRSFunctionApplication) r.getSubterm(forkPos);
                        FunctionSymbol f = fApp.getRootSymbol();

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
                        this.putMinArg(f, arg1);
                        this.putMinArg(f, arg2);
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

    private void putMinArg(FunctionSymbol f, int i) {
        boolean[] positions = this.superArgPositionsMin.get(f);
        if (positions == null) {
            positions = new boolean[f.getArity()];
            Arrays.fill(positions, false);
        }
        positions[i] = true;
        this.superArgPositionsMin.put(f, positions);
    }
}
