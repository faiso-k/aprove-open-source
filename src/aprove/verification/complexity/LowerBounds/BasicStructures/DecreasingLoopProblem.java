package aprove.verification.complexity.LowerBounds.BasicStructures;

import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.LowerBounds.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Wraps a TRS for complexity analysis and complements it with information which is relevant for Loop Detection.
 */
public class DecreasingLoopProblem extends DefaultBasicObligation {

    // the wrapped TRS
    private CpxRelTrsProblem trs;
    // the rules of the wrapped TRS
    private Set<Rule> rules;
    // the rewrite sequences that need to be analyzed
    // if todo is empty, then new rewrite sequences can be generated via narrowing
    private Set<Rule> todo;
    // the rewrite sequences that were analyzed since we applied narrowing the last time
    private Set<Rule> lastAnalyzedRules;
    // all rewrite sequences that have been analyzed so far
    private Set<Rule> allAnalyzedRules;

    public DecreasingLoopProblem(CpxRelTrsProblem trs,
            Set<Rule> rules,
            Set<Rule> todo,
            Set<Rule> lastAnalyzedRules,
            Set<Rule> allAnalyzedRules) {
        super("TRS for Loop Detection", "TRS for Loop Detection");
        if (Globals.useAssertions) {
            assert ! trs.getRewriteStrategy().contractsMultipleRedexes();
        }
        this.trs = trs;
        this.rules = rules;
        this.todo = todo;
        this.lastAnalyzedRules = lastAnalyzedRules;
        this.allAnalyzedRules = allAnalyzedRules;
    }

    public DecreasingLoopProblem setTodo(Set<Rule> todo) {
        Set<Rule> newTodo = new LinkedHashSet<>(todo);
        newTodo.removeAll(allAnalyzedRules);
        if (!trs.isDerivational()) {
            newTodo = newTodo.stream().filter(x -> trs.isBasic(x.getLeft())).collect(toSet());
        }
        return new DecreasingLoopProblem(trs, rules, newTodo, Collections.emptySet(), allAnalyzedRules);
    }

    @Override
    public String getStrategyName() {
        return "searchdecreasingloop";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return trs.getProofPurposeDescriptor();
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder();
        sb.append("Analyzing the following TRS for decreasing loops:");
        sb.append(eu.paragraph());
        sb.append(trs.export(eu));
        return sb.toString();
    }

    public boolean isDerivational() {
        return trs.isDerivational();
    }

    public Set<Rule> getLastAnalyzedRules() {
        return lastAnalyzedRules;
    }

    public Set<Rule> getRules() {
        return rules;
    }

    public boolean isInnermost() {
        return trs.getRewriteStrategy() == RewriteStrategy.INNERMOST;
    }

    public boolean STerminates() {
        return trs.STerminatesInnermost();
    }

    public Set<FunctionSymbol> getDefinedSymbols() {
        return trs.getDefinedSymbols();
    }

    public Set<HasName> getUsedNames() {
        Set<HasName> res = new LinkedHashSet<>();
        res.addAll(trs.getVariables());
        res.addAll(trs.getSignature());
        for (Rule r: todo) {
            res.addAll(r.getVariables());
        }
        return res;
    }

    public static BasicObligation initial(CpxRelTrsProblem obl) {
        Set<Rule> rules = obl.getRules().stream().map(r -> new Rule(r.getLeft(), r.getRight())).collect(toSet());
        Set<Rule> todo = obl.getR().stream().map(r -> new Rule(r.getLeft(), r.getRight())).collect(toSet());
        if (!obl.isDerivational()) {
            todo = todo.stream().filter(r -> obl.isBasic(r.getLeft())).collect(toSet());
        }
        return new DecreasingLoopProblem(obl, rules, todo, Collections.emptySet(), Collections.emptySet());
    }

    public DecreasingLoopProblem nextObligation(Set<Rule> done) {
        Set<Rule> newTodo = new LinkedHashSet<>(todo);
        newTodo.removeAll(done);
        Set<Rule> newLastAnalyzedRules = new LinkedHashSet<>(lastAnalyzedRules);
        newLastAnalyzedRules.addAll(done);
        Set<Rule> newAllAnalyzedRules = new LinkedHashSet<>(allAnalyzedRules);
        newAllAnalyzedRules.addAll(done);
        return new DecreasingLoopProblem(trs, rules, newTodo, newLastAnalyzedRules, newAllAnalyzedRules);
    }

    public DecreasingLoopProblem narrow(Abortion aborter) {
        Set<Rule> toNarrow = new LinkedHashSet<>();
        toNarrow.addAll(lastAnalyzedRules);
        toNarrow.addAll(todo);
        Set<Rule> newAllAnalyzedRules = new LinkedHashSet<>(allAnalyzedRules);
        newAllAnalyzedRules.addAll(todo);
        Set<Rule> newTodo = SimpleNarrower.narrow(rules, toNarrow, trs.getRewriteStrategy() == RewriteStrategy.INNERMOST, aborter);
        return new DecreasingLoopProblem(trs, rules, newTodo, Collections.emptySet(), newAllAnalyzedRules);
    }

    public Set<Rule> getTodo() {
        return todo;
    }

    public BasicObligation getTrs() {
        return trs;
    }

}
