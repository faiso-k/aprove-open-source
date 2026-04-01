package aprove.verification.complexity.CpxRntsProblem;

import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.CpxTypedWeightedTrsProblem.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;


/**
 * A Complexity RNTS (Recursive Natural Transition System) problem.
 *
 * This extends/modifies an IntTrsProblem (aka ITS) by the following aspects:
 * 1) Nested function applications on rhss (e.g. f(x) -> f(double(x)))
 * 2) Arithmetic on the rhs outside of funapps (e.g. f(x) -> 2 + f(2 * plus(x,y)))
 * 3) An arbitrary set of start symbols
 * 4) All lhss must use the same variables in the same order (but not necessarily the same arity)
 * 5) RNTSs only use natural numbers instead of integers as domain.
 *
 * @note multiple rhss (i.e. COM_2(f,g)) can be modeled as sums (i.e. f+g).
 *
 * A RNTS problem consists of
 *  - a set of rules
 *  - a set of initial functions
 *  - already computed results (complexity summaries for some functions)
 *  - a todo list consisting of SCCs (initially null)
 *  - a flag to indicate if partial derivations have to be considered for the complexity
 *  - a retry counter (for use with the RetryProcessor, usually 0).
 *
 * @author mnaaf
 */
public class CpxRntsProblem extends DefaultBasicObligation
  implements HasVariables, HasFunctionSymbols {

    //this constant specifies the minimal value for integers in this model, which should be 1 or 0.
    //note that this is useful for the size abstraction from TRS, where constants become either 1 or 0.
    public static final BigIntImmutable MIN_INT_VALUE = BigIntImmutable.ZERO;


    //all rules
    private final Set<RntsRule> rules;

    //the original TRS the rules originate from. Useful to apply narrowing or other TRS techniques
    //to recreate rules when no bound could be proven.
    private final CpxTypedWeightedTrsProblem trs;

    //runtime and size bounds of previous analysis steps
    private final Map<FunctionSymbol, ComplexitySummary> results;

    //initial symbols (for TRS analysis: all symbols)
    private final Set<FunctionSymbol> initial;

    //the order in which the SCCs of function symbols should be analyzed [null if not yet computed]
    private final Deque<Set<FunctionSymbol>> todo;

    //the set of defined symbols (i.e. that appear on any lhs), automatically computed
    private final Set<FunctionSymbol> definedSyms;

    //list of named arguments. Note that all functions must use the same argument names
    private final List<String> argumentNames;

    //fresh name generator for fresh variables
    private final FreshNameGenerator fngVar;

    //if we fail to prove a bound, we try several fallback strategies, this counts how many we already tried for this SCC
    private final int retryCount;

    //is it sufficient to consider complete derivations (ending in integers) or do we need to check partial derivations?
    private final boolean partialDerivations;


    private CpxRntsProblem(
            final Set<RntsRule> r,
            final CpxTypedWeightedTrsProblem trs,
            final Map<FunctionSymbol, ComplexitySummary> res,
            final Set<FunctionSymbol> s,
            final Deque<Set<FunctionSymbol>> t,
            final int c,
            final boolean partial)
    {
        super("CpxRNTS","CpxRNTS");

        this.rules = r;
        this.trs = trs;
        this.results = res;
        this.initial = s;
        this.todo = t;
        this.retryCount = c;
        this.partialDerivations = partial;

        this.definedSyms = CollectionUtils.getRootSymbols(this.rules);
        assert(this.definedSyms.containsAll(this.initial));

        List<String> argnames = new ArrayList<>();
        for (RntsRule rule : this.rules) {
            for (int i = 0; i < rule.getLeft().getRootSymbol().getArity(); ++i) {
                TRSTerm arg = rule.getLeft().getArgument(i);
                assert arg.isVariable();
                if (i < argnames.size()) {
                    assert (argnames.get(i).equals(arg.getName()));
                } else {
                    argnames.add(arg.getName());
                }
            }
        }
        this.argumentNames = argnames;

        this.fngVar = new FreshNameGenerator(this.getVariables(), FreshNameGenerator.VARIABLES);
    }

    //creates a new problem instance from the given rules. results is empty, initial is all defined symbols.
    public static CpxRntsProblem create(
            final Set<RntsRule> rules,
            final CpxTypedWeightedTrsProblem trs,
            final boolean partialDerivations) {
        return create(rules,trs,CollectionUtils.getRootSymbols(rules),partialDerivations);
    }

    //creates a new problem instance from the given rules. results is empty, initial is startSymbols.
    public static CpxRntsProblem create(
            final Set<RntsRule> rules,
            final CpxTypedWeightedTrsProblem trs,
            final Set<FunctionSymbol> startSymbols,
            final boolean partialDerivations) {
        return new CpxRntsProblem(rules,trs,new LinkedHashMap<>(),startSymbols,null,0,partialDerivations);
    }

    //clones this instance, but sets the given todo list (and resets retry count to 0)
    public CpxRntsProblem cloneWithTodo(final Deque<Set<FunctionSymbol>> todo) {
        return new CpxRntsProblem(this.rules, this.trs, this.results, this.initial, todo, 0, this.partialDerivations);
    }

    //clones this instance, but removes the current todo
    public CpxRntsProblem cloneWithTodoDone() {
        //new todo
        Deque<Set<FunctionSymbol>> newTodo = new LinkedList<>(this.todo);
        assert !newTodo.isEmpty();
        newTodo.pop();
        //new problem instance
        return new CpxRntsProblem(this.rules, this.trs, this.results, this.initial, newTodo, 0, this.partialDerivations);
    }

    //clones this instance, but clears result from current todo and increments retry counter
    public CpxRntsProblem cloneWithTodoRetry(Set<FunctionSymbol> newTodo) {
        Map<FunctionSymbol, ComplexitySummary> newResults = new LinkedHashMap<>(this.results);
        for (FunctionSymbol fun : this.getTodo()) {
            newResults.remove(fun);
        }
        Deque<Set<FunctionSymbol>> newTodos = new LinkedList<>(this.todo);
        newTodos.pop();
        newTodos.push(newTodo);;
        CpxRntsProblem res = new CpxRntsProblem(this.rules, this.trs, newResults, this.initial, newTodos, this.retryCount+1, this.partialDerivations);
        return res;
    }

    //clones this instance, but replaces the result for fun with cpx
    public CpxRntsProblem cloneWithUpdatedResult(FunctionSymbol fun, ComplexitySummary cpx) {
        //ensure fun should be analysed now
        assert this.todo.peek().contains(fun);
        //new results
        Map<FunctionSymbol, ComplexitySummary> newResults = new LinkedHashMap<>(this.results);
        newResults.put(fun, cpx);
        //new problem instance
        return new CpxRntsProblem(this.rules, this.trs, newResults, this.initial, this.todo, this.retryCount, this.partialDerivations);
    }

    //clones this instance, but uses a new set of rules (only initial nodes, analysis order and results are kept)
    public CpxRntsProblem cloneWithNewRules(final ImmutableSet<RntsRule> rules) {
        return new CpxRntsProblem(rules, this.trs, this.results, this.initial, this.todo, this.retryCount, this.partialDerivations);
    }

    //as above, but also changes the initial symbols (might be useful for new rules)
    public CpxRntsProblem cloneWithNewRules(final ImmutableSet<RntsRule> rules, final ImmutableSet<FunctionSymbol> initial) {
        return new CpxRntsProblem(rules, this.trs, this.results, initial, this.todo, this.retryCount, this.partialDerivations);
    }

    public Set<RntsRule> getRules() {
        return this.rules;
    }

    public CpxTypedWeightedTrsProblem getTrs() {
        return this.trs;
    }

    public Set<FunctionSymbol> getInitialSymbols() {
        return this.initial;
    }

    public Set<FunctionSymbol> getDefinedSymbols() {
        return this.definedSyms;
    }

    public int getMaxArity() {
        return this.argumentNames.size();
    }

    public String getArgumentName(int i) {
        assert i < this.argumentNames.size();
        return this.argumentNames.get(i);
    }

    public boolean isInitial(FunctionSymbol sym) {
        return this.initial.contains(sym);
    }

    public boolean isDefinedSymbol(FunctionSymbol sym) {
        return this.definedSyms.contains(sym);
    }

    public boolean hasAnalysisOrder() {
        return this.todo != null;
    }

    public boolean hasTodo() {
        return !this.todo.isEmpty();
    }

    public Set<FunctionSymbol> getTodo() {
        return this.todo.peek();
    }

    public int getRetryCount() {
        return this.retryCount;
    }

    public boolean allowsPartialDerivations() {
        return this.partialDerivations;
    }

    //returns all rules of the form fun(...) -> r
    public Set<RntsRule> getRulesFrom(FunctionSymbol fun) {
        Set<RntsRule> res = new HashSet<>();
        for (RntsRule rule : this.rules) {
            if (rule.getRootSymbol().equals(fun)) {
                res.add(rule);
            }
        }
        return res;
    }

    public boolean hasVariable(TRSVariable var) {
        return this.argumentNames.contains(var.getName());
    }

    public TRSVariable generateFreshVariable(String basename, boolean useMemory) {
        return TRSTerm.createVariable(this.fngVar.getFreshName(basename, useMemory));
    }

    public boolean hasDefinedSymbols(TRSTerm TRSTerm) {
        // why does java not have intersection?!
        return TRSTerm.getFunctionSymbols().stream().anyMatch(f -> this.definedSyms.contains(f));
    }

    //returns true iff the given rule is terminating, i.e. no defined symbols on the right
    public boolean isTerminating(RntsRule rule) {
        return !hasDefinedSymbols(rule.getRight());
    }

    //returns true iff the given function is terminating, i.e. all its rules are terminating
    public boolean isTerminating(FunctionSymbol fun) {
        return getRulesFrom(fun).stream().allMatch(r -> this.isTerminating(r));
    }

    //returns true iff the function symbol f has already been analyzed
    public boolean hasResult(FunctionSymbol f) {
        return this.results.containsKey(f);
    }

    //returns the result of the previous analysis of f (size and runtime bound)
    //NOTE: throws if f has not been analyzed (check with hasResult())
    public ComplexitySummary getResult(FunctionSymbol f) {
        assert this.hasResult(f);
        return this.results.get(f);
    }

    @Override
    public Set<TRSVariable> getVariables() {
        Set<TRSVariable> vars = new HashSet<>();
        for (RntsRule rule : this.rules) {
            vars.addAll(rule.getVariables());
        }
        return vars;
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        Set<FunctionSymbol> funs = new HashSet<>();
        for (RntsRule rule : this.rules) {
            funs.addAll(rule.getFunctionSymbols());
        }
        return funs;
    }

    public Set<FunctionSymbol> getFunctionSymbolsOnRhs() {
        Set<FunctionSymbol> funs = new HashSet<>();
        for (RntsRule rule : this.rules) {
            funs.addAll(rule.getRight().getFunctionSymbols());
        }
        return funs;
    }

    @Override
    public String getStrategyName() {
        return "rnts";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this, "runtime complexity");
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder s = new StringBuilder();
        s.append(eu.escape("Complexity RNTS consisting of the following rules:"));
        s.append(eu.cond_linebreak());

        //sort (inefficient but more readable for debugging/proof output)
        List<RntsRule> sortedRules = this.rules.stream().sorted((a,b) -> {
            int lhs = a.getRootSymbol().compareTo(b.getRootSymbol());
            if (lhs != 0) return lhs;
            return a.getRight().compareTo(b.getRight());
        }).collect(Collectors.toList());

        s.append(eu.set(sortedRules,Export_Util.RULES));
        s.append(eu.cond_linebreak());

        if (!this.allowsPartialDerivations()) {
            s.append(eu.escape("Only complete derivations are relevant for the runtime complexity."));
            s.append(eu.linebreak());
        }

        //only print start symbols if not all symbols are initial
        if (this.initial.size() != this.definedSyms.size()) {
            s.append(eu.escape("The start-symbols are: "));
            s.append(eu.escape(this.initial.stream().map(f -> f.export(eu)).collect(Collectors.joining(", "))));
            s.append(eu.paragraph());
        }

        if (this.todo != null) {
            s.append(eu.export("Function symbols to be analyzed: "));
            s.append(this.todo.stream().map(funset ->
                eu.escape("{") + funset.stream().map(f -> f.export(eu)).collect(Collectors.joining(",")) + eu.escape("}")
            ).collect(Collectors.joining(", ")));
            s.append(eu.cond_linebreak());
        }

        if (!this.results.isEmpty()) {
            s.append(eu.export("Previous analysis results are:") + eu.linebreak());
            StringBuilder resultStr = new StringBuilder();
            for (Entry<FunctionSymbol, ComplexitySummary> entry : this.results.entrySet()) {
                resultStr.append(eu.escape("  ")); //for plain text output, where indent does not work
                resultStr.append(entry.getKey().export(eu));
                resultStr.append(eu.escape(": "));
                resultStr.append(entry.getValue().export(eu));
                resultStr.append(eu.linebreak());
            }
            s.append(eu.indent(resultStr.toString()));
        }
        return s.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

}

