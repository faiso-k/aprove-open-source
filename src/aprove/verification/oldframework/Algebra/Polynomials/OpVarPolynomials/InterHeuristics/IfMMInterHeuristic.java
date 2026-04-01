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
 * Allows max(x_i, x_j) in the interpretation of f if i != j and there is
 * a term f(t_1, t_2, t_3) on a lhs of P \cup R such that t_i and t_j are
 * variables (i != j) and t_k is a constant (k != i and k != j), thus
 * suspiciously making f look like something that works like "if" or "IF").
 *
 * @author fuhs
 * @version $Id$
 */
public class IfMMInterHeuristic implements MMInterHeuristic {

    private Map<FunctionSymbol, Collection<Pair<Integer, Integer>>> maxSyms;

    public IfMMInterHeuristic() {
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f) {
        Collection<Pair<Integer, Integer>> result = this.maxSyms.get(f);
        if (result == null) {
            result = java.util.Collections.emptySet();
        }
        return result;
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f) {
        return java.util.Collections.emptySet();
    }

    @Override
    public void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {
        this.reset();
        this.addNewData(r);
        this.addNewData(p);
    }

    private void reset() {
        this.maxSyms = new HashMap<FunctionSymbol, Collection<Pair<Integer, Integer>>>();
    }

    private void addNewData(Set<? extends GeneralizedRule> rules) {
        for (GeneralizedRule rule : rules) {
            TRSFunctionApplication l = rule.getLeft();
            FunctionSymbol f = l.getRootSymbol();
            if (f.getArity() == 3) {
                // candidate for "if"-like symbol
                int seenVars = 0;
                int posConst = -1; // -1 means "unset"

                List<? extends TRSTerm> args = l.getArguments();

                {
                    TRSTerm t0 = args.get(0);
                    if (t0.isVariable()) {
                        ++seenVars;
                    }
                    else if ( ((TRSFunctionApplication) t0).getRootSymbol().getArity() == 0) {
                        posConst = 0;
                    }
                    else {
                        continue;
                    }
                }
                {
                    TRSTerm t1 = args.get(1);
                    if (t1.isVariable()) {
                        ++seenVars;
                    }
                    else if ( ((TRSFunctionApplication) t1).getRootSymbol().getArity() == 0) {
                        if (posConst == -1) {
                            posConst = 1;
                        }
                        else {
                            continue;
                        }
                    }
                    else {
                        continue;
                    }
                }
                {
                    TRSTerm t2 = args.get(2);
                    if (t2.isVariable()) {
                        if (seenVars == 1) {
                            ++seenVars;
                        }
                        else {
                            // 1 var or 3 vars in total are not okay
                            continue;
                        }
                    }
                    else if ( ((TRSFunctionApplication) t2).getRootSymbol().getArity() == 0) {
                        if (posConst == -1) {
                            posConst = 2;
                        }
                        else {
                            continue;
                        }
                    }
                    else {
                        continue;
                    }
                }

                // one final check now that we have got *this* far
                if (Globals.useAssertions) {
                    assert seenVars == 2;
                    assert posConst != -1;
                }

                Collection<Pair<Integer, Integer>> maxPairs = this.maxSyms.get(f);
                if (maxPairs == null) {
                    maxPairs = new LinkedHashSet<Pair<Integer, Integer>>(3);
                    this.maxSyms.put(f, maxPairs);
                }
                switch (posConst) {
                case 0:
                    maxPairs.add(new Pair<Integer, Integer>(1, 2));
                    break;
                case 1:
                    maxPairs.add(new Pair<Integer, Integer>(0, 2));
                    break;
                case 2:
                    maxPairs.add(new Pair<Integer, Integer>(0, 1));
                    break;
                default:
                    if (Globals.useAssertions) {
                        assert false : "Ternary symbol has arg at position " +
                            posConst + "!";
                    }
                }
            }
        }
    }


}
