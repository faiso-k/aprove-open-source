package aprove.verification.oldframework.IRSwT.Sorts;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Given a set of rules. Analyze what sort occur at which position.
 * @author Matthias Hoelzel
 *
 */
public class SortAnalyzer {
    /** Set of rules we are going to analyze */
    private final LinkedHashSet<IGeneralizedRule> rules;

    /** Set of non-arithmetical symbols occurring in rules */
    private final LinkedHashSet<FunctionSymbol> symbols;

    /** Information about the sorts gathered so far */
    private LinkedHashMap<FunctionSymbol, ArrayList<Sort>> dict;

    /** Set of non-pure symbols, i.e., symbols below which an integer might occur. */
    private final LinkedHashSet<FunctionSymbol> nonPureSymbols;

    /** Stores the terms that occur in a given rule as i-th arguments of
     * a given symbol g. */
    private LinkedHashMap<Pair<IGeneralizedRule, FunctionSymbol>, ArrayList<LinkedHashSet<TRSTerm>>> arguments;

    /** Result */
    private SortDictionary result;

    /**
     * Constructor!
     * @param inputRules set of rules
     */
    public SortAnalyzer(final Set<IGeneralizedRule> inputRules) {
        this.rules = new LinkedHashSet<>(inputRules);
        this.symbols = new LinkedHashSet<>();
        this.nonPureSymbols = new LinkedHashSet<>();
    }

    /**
     * Runs the analysis and returns a sort dictionary
     * @return sort dictionary
     */
    public SortDictionary analyze() {
        if (this.result != null) {
            return this.result;
        }

        // 1. Find symbols
        this.findSymbols();

        // 2. Initialized data structures
        this.initDataStructures();

        // 3. Run analysis
        this.runAnalysis();

        // 4. Return result
        this.result = new SortDictionary(this.dict);
        return this.result;
    }

    /**
     * Finds occurring symbols.
     */
    private void findSymbols() {
        for (final IGeneralizedRule rule : this.rules) {
            this.collectSymbols(rule.getLeft());
            this.collectSymbols(rule.getRight());
        }
    }

    /**
     * Collect the non-arithmetical symbols occurring in the given terms
     * and adds them into field symbols.
     * @param t some term
     */
    private void collectSymbols(final TRSTerm t) {
        if (t instanceof TRSVariable) {
            return;
        }
        assert t instanceof TRSFunctionApplication;

        final TRSFunctionApplication func = (TRSFunctionApplication) t;
        final FunctionSymbol f = func.getRootSymbol();
        if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(f)) {
            this.symbols.add(f);
            for (final TRSTerm arg : func.getArguments()) {
                this.collectSymbols(arg);
            }
        }
    }

    /**
     * Initializes the data structures.
     */
    private void initDataStructures() {
        // Initialize dictionary
        this.dict = new LinkedHashMap<>();
        for (final FunctionSymbol f : this.symbols) {
            final ArrayList<Sort> sorts = new ArrayList<>();
            for (int i = 0; i < f.getArity(); i++) {
                sorts.add(Sort.VARIABLE);
            }
            this.dict.put(f, sorts);
        }

        // Initialize argument lists:
        this.arguments = new LinkedHashMap<>();
        for (final IGeneralizedRule rule : this.rules) {
            for (final FunctionSymbol sym : this.symbols) {
                final ArrayList<LinkedHashSet<TRSTerm>> argumentLists = new ArrayList<>(sym.getArity());
                for (int i = 0; i < sym.getArity(); i++) {
                    final LinkedHashSet<TRSTerm> newSet = new LinkedHashSet<>();
                    argumentLists.add(newSet);
                }

                final Pair<IGeneralizedRule, FunctionSymbol> indexPair = new Pair<>(rule, sym);
                this.arguments.put(indexPair, argumentLists);
            }
        }
        // and fill in some useful content:
        for (final IGeneralizedRule rule : this.rules) {
            this.collectArguments(rule, rule.getLeft());
            this.collectArguments(rule, rule.getRight());
        }
    }

    /**
     * Collects the arguments and adds them into our data structure.
     * @param rule current rule
     * @param t current term
     */
    private void collectArguments(final IGeneralizedRule rule, final TRSTerm t) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                final ImmutableList<TRSTerm> argList = func.getArguments();
                for (int i = 0; i < argList.size(); i++) {
                    final TRSTerm currentArg = argList.get(i);
                    final Pair<IGeneralizedRule, FunctionSymbol> indexPair = new Pair<>(rule, sym);
                    this.arguments.get(indexPair).get(i).add(currentArg);
                    this.collectArguments(rule, currentArg);
                }
            }
        }
    }

    /**
     * Analyzes the sorts of the given rules.
     */
    private void runAnalysis() {
        // 1. Find positions where integers occur for sure:
        this.findIntegers();
        // 2. Find positions where integer may occur:
        this.findMixedPositions();
    }

    /**
     * Finds and adds positions where integer occur.
     */
    private void findIntegers() {
        for (final FunctionSymbol sym : this.symbols) {
            for (int p = 0; p < sym.getArity(); p++) {
                boolean integer = true;
                analysis: for (final IGeneralizedRule rule : this.rules) {
                    final Pair<IGeneralizedRule, FunctionSymbol> indexPair = new Pair<>(rule, sym);
                    for (final TRSTerm arg : this.arguments.get(indexPair).get(p)) {
                        if (!this.isDefinitelyInteger(rule, arg)) {
                            integer = false;
                            break analysis;
                        }
                    }
                }
                if (integer) {
                    this.setSort(sym, p, Sort.INTEGER);
                }
            }
        }
    }

    /**
     * Updates our dictionary with the given parameters.
     * @param sym a function symbol
     * @param position a position >= 0, < arity of the symbol
     * @param sort the new sort
     */
    private void setSort(final FunctionSymbol sym, final int position, final Sort sort) {
        if (sort != Sort.FUNAPP && sort != Sort.VARIABLE) {
            this.nonPureSymbols.add(sym);
        }
        this.dict.get(sym).set(position, sort);
    }

    /**
     * Finds and adds positions where (or below that point) an integer might occur.
     */
    private void findMixedPositions() {
        boolean changed = true;
        while (changed) {
            changed = false;
            for (final FunctionSymbol sym : this.symbols) {
                for (int p = 0; p < sym.getArity(); p++) {
                    if (this.dict.get(sym).get(p) == Sort.FUNAPP) {
                        for (final IGeneralizedRule rule : this.rules) {
                            final Pair<IGeneralizedRule, FunctionSymbol> indexPair = new Pair<>(rule, sym);
                            for (final TRSTerm arg : this.arguments.get(indexPair).get(p)) {
                                if (this.canBeInteger(rule, arg)) {
                                    this.setSort(sym, p, Sort.EVERYTHING);
                                    changed = true;
                                }
                                if (arg instanceof TRSFunctionApplication) {
                                    final TRSFunctionApplication func = (TRSFunctionApplication) arg;
                                    if (this.nonPureSymbols.contains(func.getRootSymbol())) {
                                        this.setSort(sym, p, Sort.EVERYTHING);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * Returns true, if we are sure that it is an integer.
     * @param currentRule the current rule
     * @param v some term
     * @return boolean
     */
    private boolean isDefinitelyInteger(final IGeneralizedRule currentRule, final TRSTerm v) {
        if (v instanceof TRSFunctionApplication) {
            final FunctionSymbol f = ((TRSFunctionApplication) v).getRootSymbol();
            return IDPPredefinedMap.DEFAULT_MAP.isPredefined(f) && f.getArity() > 0;
        } else {
            assert v instanceof TRSVariable;
            if (currentRule.getCondTerm() != null && currentRule.getCondTerm().getVariables().contains(v)) {
                return true;
            }
            final LinkedList<Sort> infections = new LinkedList<>();
            infections.add(Sort.INTEGER);
            return this.checkForInfection(currentRule, (TRSVariable) v, infections);
        }
    }

    /**
     * Checks whether it is possible that t is actually an integer.
     * @param currentRule currently considered rule
     * @param v some term
     * @return boolean
     */
    private boolean canBeInteger(final IGeneralizedRule currentRule, final TRSTerm v) {
        if (v instanceof TRSFunctionApplication) {
            final FunctionSymbol f = ((TRSFunctionApplication) v).getRootSymbol();
            return IDPPredefinedMap.DEFAULT_MAP.isPredefined(f);
        } else {
            assert v instanceof TRSVariable;
            if (currentRule.getCondTerm() != null && currentRule.getCondTerm().getVariables().contains(v)) {
                return true;
            }
            final LinkedList<Sort> infections = new LinkedList<>();
            infections.add(Sort.INTEGER);
            infections.add(Sort.EVERYTHING);
            return this.checkForInfection(currentRule, (TRSVariable) v, infections);
        }
    }

    /**
     * Checks whether or this a given variable occur in a given rule with one of the specified sorts.
     * @param currentRule the currently considered rule
     * @param v some variable
     * @param infectionSorts some sorts that may carry over to other positions
     * @return boolean
     */
    private boolean checkForInfection(
        final IGeneralizedRule currentRule,
        final TRSVariable v,
        final Collection<Sort> infectionSorts)
    {
        for (final FunctionSymbol sym : this.symbols) {
            for (int i = 0; i < sym.getArity(); i++) {
                final Sort s = this.dict.get(sym).get(i);
                if (infectionSorts.contains(s)) {
                    final Pair<IGeneralizedRule, FunctionSymbol> indexPair = new Pair<>(currentRule, sym);
                    for (final TRSTerm arg : this.arguments.get(indexPair).get(i)) {
                        if (arg.isVariable() && arg.equals(v)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }
}
