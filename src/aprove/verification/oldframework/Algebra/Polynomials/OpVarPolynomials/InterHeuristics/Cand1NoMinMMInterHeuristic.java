package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Duplicate of Cand1MMInterHeuristic which only allows max.
 * @author Ulrich Schmidt-Goertz
 */
public class Cand1NoMinMMInterHeuristic extends Cand1MMInterHeuristic {

    public Cand1NoMinMMInterHeuristic() {
    }

    /**
     * Never use min.
     * @param f not used.
     * @return an empty set.
     */
    @Override
    public Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f) {
        return java.util.Collections.emptySet();
    }
}
