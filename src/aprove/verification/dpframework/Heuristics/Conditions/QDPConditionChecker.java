package aprove.verification.dpframework.Heuristics.Conditions;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * QDPConditionChecker.<br><br>
 *
 * Created: May 8, 2007<br>
 * Last modified: May 8, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public class QDPConditionChecker {

    /**
     * Computes a Map from Rules to a List of Positions where the rhs of the
     * Rule has an argument which contains at least one variable which occurs in
     * at least one other argument of the rhs of the Rule and in at least one
     * successor of the Rule in the specified QDP there is a ground term on this
     * Position in the lhs of the successor Rule in the specified QDP while this
     * lhs has the same root symbol as the rhs before.
     * @param qdp The QDP to compute the resulting Map from.
     * @return A Map from Rules to Lists of Positions which hold a certain
     * heuristic condition.
     */
    public static Map<Rule, Set<Position>> computeMapOfPositionsWithCondition(QDPProblem qdp) {
        Map<Rule, Set<Position>> res = new LinkedHashMap<Rule, Set<Position>>();
        ImmutableSet<FunctionSymbol> defSymbols = qdp.getRwithQ().getDefinedSymbolsOfR();
        for (Node<Rule> node : qdp.getDependencyGraph().getGraph().getNodes()) {
            Set<Position> positions = new LinkedHashSet<Position>();
            TRSTerm rhs = node.getObject().getRight();
            if (rhs != null && rhs instanceof TRSFunctionApplication) {
                TRSFunctionApplication right = (TRSFunctionApplication)rhs;
                ImmutableList<? extends TRSTerm> args = right.getArguments();
                int arity = args.size();
                List<Integer> candidates = new ArrayList<Integer>();
                for (int i = 0; i < arity; i++) {
                    TRSTerm arg = right.getArgument(i);
                    Set<TRSVariable> vars = arg.getVariables();
                    for (int j = 0; j < arity; j++) {
                        if (i == j) {
                            continue;
                        } else {
                            Set<TRSVariable> otherVars = right.getArgument(j).getVariables();
                            otherVars.retainAll(vars);
                            if (!otherVars.isEmpty()) {
                                candidates.add(i);
                                break;
                            }
                        }
                    }
                }
                if (!candidates.isEmpty()) {
                    Set<Node<Rule>> nodes = qdp.getDependencyGraph().getGraph().getOut(node);
                    if (nodes != null && !nodes.isEmpty()) {
                        for (Node<Rule> succ : nodes) {
                            TRSFunctionApplication lhs =
                                succ.getObject().getLeft();
                            if (right.getRootSymbol().equals(
                                lhs.getRootSymbol())) {
                                for (Integer i : candidates) {
                                    if (QDPConditionChecker.isGround(defSymbols, lhs.getArgument(i))) {
                                        Position pos = Position.create();
                                        pos = pos.append(i);
                                        positions.add(pos);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if (!positions.isEmpty()) {
                res.put(node.getObject(), positions);
            }
        }
        //        System.err.println(res);
        return res;
    }

    /**
     * Checks whether or not the specified term is ground concerning the
     * specified set of defined FunctionSymbols.
     * @param defSymbols ImmutableSet of all defined FunctionSymbols.
     * @param argument Term to check.
     * @return True, if argument is ground. False otherwise.
     */
    private static boolean isGround(ImmutableSet<FunctionSymbol> defSymbols, TRSTerm argument) {
        if (argument.isVariable()) {
            return false;
        } else {
            TRSFunctionApplication func = (TRSFunctionApplication)argument;
            if (defSymbols.contains(func.getRootSymbol())) {
                return false;
            }
            for (TRSTerm arg : func.getArguments()) {
                if (!QDPConditionChecker.isGround(defSymbols, arg)) {
                    return false;
                }
            }
        }
        return true;
    }

}
