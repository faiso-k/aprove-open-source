package aprove.verification.complexity.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class RuleSet implements HasRules<Rule>, HasDefinedSymbols {

    ImmutableSet<Rule> rules;
    ImmutableSet<FunctionSymbol> definedSymbols;

    public RuleSet(ImmutableSet<Rule> rules, ImmutableSet<FunctionSymbol> definedSymbols) {
        this.rules = rules;
        this.definedSymbols = definedSymbols;
    }

    public boolean isDefined(FunctionSymbol f) {
        return definedSymbols.contains(f);
    }

    public boolean isBasic(TRSTerm tArg) {
        if (tArg.isVariable()) {
            return false;
        }
        TRSFunctionApplication t = (TRSFunctionApplication) tArg;
        if (!definedSymbols.contains(t.getRootSymbol())) {
            return false;
        }
        return t.getNonRootFunctionSymbols().stream().allMatch(x -> !definedSymbols.contains(x));
    }

    @Override
    public ImmutableSet<FunctionSymbol> getDefinedSymbols() {
        return definedSymbols;
    }

    @Override
    public ImmutableSet<Rule> getRules() {
        return rules;
    }

    public Set<String> getUsedNames() {
        var res = new LinkedHashSet<String>();
        for (var x : definedSymbols) {
            res.add(x.getName());
        }
        for (var r : rules) {
            for (var x : r.getVariables()) {
                res.add(x.getName());
            }
            for (var x : r.getFunctionSymbols()) {
                res.add(x.getName());
            }
        }
        return res;
    }

    public boolean isOverlaySystem() {
        for (Pair<Rule, Rule> p : Collection_Util.getPairs(rules)) {
            TRSTerm l1 = p.x.getLeft();
            TRSTerm l2 = p.y.getLeft();
            for (Pair<?, TRSFunctionApplication> p2 : l1.getNonRootNonVariablePositionsWithSubTerms()) {
                TRSTerm t = p2.y.renameVariables(l2.getVariables());
                if (t.unifies(l2)) {
                    return false;
                }
            }
            for (Pair<?, TRSFunctionApplication> p2 : l2.getNonRootNonVariablePositionsWithSubTerms()) {
                TRSTerm t = p2.y.renameVariables(l1.getVariables());
                if (t.unifies(l1)) {
                    return false;
                }
            }
        }
        return true;
    }

}
