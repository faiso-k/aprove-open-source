package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * @author fuhs
 * @author micpar
 * @version $Id: MonotonicityCalculator.java,v 1.3 2008/09/29 14:42:51 micpar
 *          Exp $
 */
public class MonotonicityCalculator {

    /**
     * @param decreasingSymbol
     * @param rules
     * @param dpRightHandSide
     * @return monotonicity constraint needed by POLO or other processor in order
     *         to find correct order
     */
    public MonotonicityConstraints calculateRequirements(FunctionSymbol decreasingSymbol, ImmutableSet<Rule> rules, TRSTerm dpRightHandSide) {
        // Compute Set of Functions which must not be filtered
        Set<FunctionSymbol> notFilteredFunctions = new LinkedHashSet<FunctionSymbol>();
        notFilteredFunctions.add(decreasingSymbol);
        Set<FunctionSymbol> temp = new LinkedHashSet<FunctionSymbol>();
        // Fix-point style computation
        do {
            temp.addAll(notFilteredFunctions);
            for (Rule rule : rules) {
                for (FunctionSymbol funSym : temp) {
                    if (rule.getRight().getFunctionSymbols().contains(funSym)) {
                        notFilteredFunctions.add(rule.getRootSymbol());
                    }
                }
            }
        }
        while (!temp.equals(notFilteredFunctions));

        // Now compute arguments which must not be filtered
        Map<FunctionSymbol, Set<Integer>> reqs = new LinkedHashMap<FunctionSymbol, Set<Integer>>();

        List<TRSTerm> rightHandSides = new ArrayList<TRSTerm>();
        for (Rule rule : rules) {
            rightHandSides.add(rule.getRight());
        }

        rightHandSides.add(dpRightHandSide);

        for (TRSTerm rhs : rightHandSides) {
            // Iterate through positions and remove those where there are no
            // "not filtered" function symbols
            Set<Position> positions = rhs.getPositions();
            Iterator<Position> posIter = positions.iterator();
            while (posIter.hasNext()) {
                Position pos = posIter.next();
                if (pos.isEmptyPosition()) {
                    posIter.remove();
                }
                else if (!rhs.getSubterm(pos).isVariable()) {
                    if (!notFilteredFunctions.contains(((TRSFunctionApplication) rhs.getSubterm(pos)).getRootSymbol())) {
                        posIter.remove();
                    }
                }
                else {
                    posIter.remove();
                }
            }
            // Iterate through resulting positions and put requirements in a map
            for (Position position : positions) {
                TRSFunctionApplication funApp = (TRSFunctionApplication) rhs;
                int index = 0;
                for (Integer arg : position) {
                    // Cut off the position right before arg
                    // We need this in order to get the right function symbol
                    Position prefix = position.shorten(position.getDepth() - index);
                    // If subterm is not variable (cannot occur actually), then
                    // add the root symbol and forbid filtering of arg
                    TRSTerm subterm = funApp.getSubterm(prefix);
                    if (!subterm.isVariable()) {
                        FunctionSymbol funSym = ((TRSFunctionApplication) subterm).getRootSymbol();
                        Set<Integer> args = null;
                        if (reqs.containsKey(funSym)) {
                            args = reqs.get(funSym);
                        }
                        else {
                            args = new LinkedHashSet<Integer>();
                        }
                        args.add(arg);
                        reqs.put(funSym, args);
                    }
                    index++;
                }
            }
        }
        Map<FunctionSymbol, ImmutableSet<Integer>> tempMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<Integer>>();
        for (Map.Entry<FunctionSymbol, Set<Integer>> entry : reqs.entrySet()) {
            tempMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        return MonotonicityConstraints.create(ImmutableCreator.create(tempMap));
    }
}
