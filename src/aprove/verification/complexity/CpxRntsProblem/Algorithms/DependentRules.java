package aprove.verification.complexity.CpxRntsProblem.Algorithms;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Helper functions to find all rules that are relevant for the runtime of
 * a given function f. These rules are computed as follows:
 *
 * (1) All rules with root symbol f,
 * (2) All rules where the root symbol occurs on any rhs of the relevant rules,
 *     unless the root symbol has already been analyzed.
 *
 * @author mnaaf
 *
 */
public abstract class DependentRules {

    private static boolean isTodo(FunctionSymbol fun, CpxRntsProblem rnts) {
        if (rnts.hasResult(fun)) {
            return !rnts.getResult(fun).hasRuntime();
        }
        return true;
    }

    private static Set<RntsRule> collectTodoRuleClosure(Set<FunctionSymbol> funs, CpxRntsProblem rnts) {
        Set<FunctionSymbol> done = new LinkedHashSet<>();
        Set<FunctionSymbol> curr = funs;

        Set<RntsRule> res = new LinkedHashSet<>();
        while (!curr.isEmpty()) {
            Set<FunctionSymbol> next = new LinkedHashSet<>();

            for (RntsRule rule : rnts.getRules()) {
                if (curr.contains(rule.getRootSymbol())) {
                    res.add(rule);
                    next.addAll(rule.getFunctionSymbols());
                }
            }

            done.addAll(curr);
            next.removeAll(done);
            curr = next.stream().filter(f -> isTodo(f,rnts)).collect(Collectors.toSet());
        }
        return res;
    }

    public static Set<RntsRule> getTodoRuleClosureFrom(FunctionSymbol fun, CpxRntsProblem rnts) {
        assert isTodo(fun,rnts) : fun + " unexpectedly not in Todo for " + rnts;
        return collectTodoRuleClosure(Collections.singleton(fun), rnts);
    }
}
