package aprove.verification.complexity.LowerBounds.BasicStructures;

import static aprove.verification.oldframework.Utility.Collection_Util.*;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public class Trs implements Exportable, HasRules<Rule>, HasDefinedSymbols {

    private Set<Rule> rules;
    Set<FunctionSymbol> constructors = new LinkedHashSet<>();
    Set<FunctionSymbol> definedSymbols = new LinkedHashSet<>();
    private DependencyGraph<Trs> depGraph;
    private boolean innermost;

    public Trs(Set<Rule> rules, boolean innermost) {
        this.rules = rules;
        this.initSignature();
        this.depGraph = new DependencyGraph<Trs>(this);
        this.innermost = innermost;
    }

    private void initSignature() {
        for (Rule r : rules) {
            this.definedSymbols.add(r.getRootSymbol());
            this.constructors.addAll(r.getFunctionSymbols());
        }
        this.constructors.removeAll(this.definedSymbols);
    }

    public DependencyGraph<Trs> getDependencyGraph() {
        return this.depGraph;
    }

    @Override
    public Set<FunctionSymbol> getDefinedSymbols() {
        return this.definedSymbols;
    }

    public Set<FunctionSymbol> getConstructors() {
        return this.constructors;
    }

    public Set<FunctionSymbol> getSignature() {
        Set<FunctionSymbol> res = new LinkedHashSet<>();
        res.addAll(this.constructors);
        res.addAll(this.definedSymbols);
        return res;
    }

    public Set<TRSVariable> getVariables() {
        Set<TRSVariable> variables = new LinkedHashSet<>();
        for (AbstractRule r : rules) {
            variables.addAll(r.getVariables());
        }
        return variables;
    }

    @Override
    public Set<Rule> getRules() {
        return this.rules;
    }

    public Set<String> getUsedNames() {
        Set<String> res = new LinkedHashSet<>();
        for (FunctionSymbol symbol : this.getSignature()) {
            res.add(symbol.getName());
        }
        for (TRSVariable var : this.getVariables()) {
            res.add(var.getName());
        }
        return res;
    }

    /**
     * Used to decide which function symbols occur in generator equations. As we are interested in runtime complexity,
     * only rules with basic left-hand sides are taken into account.
     */
    public boolean usedForPatternMatchingInRecursicveRule(FunctionSymbol s, DependencyGraph<?> depGraph) {
        for (Rule r : rules) {
            if (isBasic(r.getLeft()) && r.getLeft().getFunctionSymbols().contains(s) && depGraph.isRecursive(r)) {
                return true;
            }
        }
        return false;
    }

    /*
     * Used to decide which function symbols occur in generator equations. As we are interested in runtime complexity,
     * only rules with basic left-hand sides are taken into account.
     */
    public boolean usedForPatternMatchingInNonRecursicveRule(FunctionSymbol s, DependencyGraph<?> depGraph) {
        for (Rule r : rules) {
            if (isBasic(r.getLeft()) && r.getLeft().getFunctionSymbols().contains(s) && !depGraph.isRecursive(r)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Used to decide which function symbols occur in generator equations. As we are interested in runtime complexity,
     * only rules with basic left-hand sides are taken into account.
     */
    public boolean usedForPatternMatching(FunctionSymbol s) {
        for (Rule r : rules) {
            if (isBasic(r.getLeft()) && r.getLeft().getFunctionSymbols().contains(s)) {
                return true;
            }
        }
        return false;
    }

    private boolean isBasic(TRSFunctionApplication left) {
        return definedSymbols.contains(left.getRootSymbol())
               && left.getArguments().stream().allMatch(x -> areDisjoint(definedSymbols, x.getFunctionSymbols()));
    }

    public int numberOfRulesFor(FunctionSymbol symbol) {
        int res = 0;
        for (Rule r: rules) {
            if (r.getRootSymbol().equals(symbol)) {
                res++;
            }
        }
        return res;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder();
        if (this.innermost) {
            sb.append(eu.escape("Innermost TRS:"));
        } else {
            sb.append(eu.escape("TRS:"));
        }
        sb.append(eu.linebreak());
        sb.append(eu.escape("Rules:"));
        sb.append(eu.linebreak());
        for (AbstractRule r: this.rules) {
            sb.append(eu.export(r));
            sb.append(eu.linebreak());
        }
        return sb.toString();
    }

    public boolean isInnermost() {
        return this.innermost;
    }
}
