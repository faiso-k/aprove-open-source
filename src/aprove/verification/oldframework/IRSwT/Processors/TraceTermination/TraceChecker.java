package aprove.verification.oldframework.IRSwT.Processors.TraceTermination;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Enumerates traces and checks whether or not they have relatively terminating rules.
 * @author Matthias Hoelzel
 */
public class TraceChecker {
    private final LinkedHashSet<IGeneralizedRule> inputRules;

    private final LinkedHashSet<IGeneralizedRule> transformedRules;

    private final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> history;

    private final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> invertedTraceHistory;

    private final LinkedHashSet<FunctionSymbol> symbols;

    private final LinkedHashSet<FunctionSymbol> definedSymbols;

    private final LinkedList<Way> ways;

    private final FreshNameGenerator fng;

    private final Abortion aborter;

    private Trace successfulTrace;

    private LinkedHashSet<IGeneralizedRule> relativelyNonTerminatingRules;

    /**
     * Constructor!
     * @param rules input problem
     * @param gen
     * @param abortion
     */
    public TraceChecker(
        final LinkedHashSet<IGeneralizedRule> rules,
        final FreshNameGenerator gen,
        final Abortion abortion)
    {
        this.inputRules = rules;
        this.transformedRules = new LinkedHashSet<>();
        this.history = new LinkedHashMap<>();
        this.invertedTraceHistory = new LinkedHashMap<>();
        this.fng = gen;
        this.aborter = abortion;
        this.symbols = new LinkedHashSet<>();
        this.definedSymbols = new LinkedHashSet<>();
        this.ways = new LinkedList<>();
    }

    public Trace getTraceOfSuccess() {
        return this.successfulTrace;
    }

    public LinkedHashSet<IGeneralizedRule> getRelativelyNonTerminatingTraceRules() {
        return this.relativelyNonTerminatingRules;
    }

    /**
     * Hunts for a trace with some relatively terminating rule.
     * In case of success, it return a smaller problem.
     * Otherwise: null.
     * @return set of rules
     * @throws AbortionException can be aborted
     */
    public LinkedHashSet<IGeneralizedRule> followTraces() throws AbortionException {
        // 1. Eliminate constants
        this.eliminateConstants();

        // 2. Enumerate the ways
        this.enumerateWays();

        // 3. Hunting:
        return this.hunt();
    }

    private LinkedHashSet<IGeneralizedRule> hunt() throws AbortionException {
        // 1. Check trivial traces:
        for (final Way w : this.ways) {
            this.aborter.checkAbortion();
            final Trace t = this.generateTrivialTrace(w);
            final RelativeNonTerminationFinder rtf = new RelativeNonTerminationFinder(t, this.aborter);
            final LinkedHashSet<IGeneralizedRule> relativelyNonTerminating = rtf.findRelativelyNonTerminatingRules();
            if (rtf.wasSuccessful()) {
                return this.generateResult(t, relativelyNonTerminating);
            }
        }

        return null;
    }

    private LinkedHashSet<IGeneralizedRule> generateResult(
        final Trace t,
        final LinkedHashSet<IGeneralizedRule> relativelyNonTerminating)
    {
        this.successfulTrace = t;
        this.relativelyNonTerminatingRules = relativelyNonTerminating;

        final LinkedHashSet<IGeneralizedRule> resultRules = new LinkedHashSet<>();
        for (final IGeneralizedRule traceRule : relativelyNonTerminating) {
            for (final IGeneralizedRule transformedRule : this.transformedRules) {
                if (this.invertedTraceHistory.get(transformedRule).equals(traceRule)) {
                    resultRules.add(this.history.get(transformedRule));
                }
            }
        }
        return resultRules;
    }

    private Trace generateTrivialTrace(final Way w) {
        final LinkedHashSet<IGeneralizedRule> traceRules = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : this.transformedRules) {
            final IGeneralizedRule traceRule = Way.applyWays(rule, w, w);
            this.invertedTraceHistory.put(rule, traceRule);
            traceRules.add(traceRule);
        }
        return new Trace(ImmutableCreator.create(traceRules));
    }

    private void eliminateConstants() {
        for (final IGeneralizedRule rule : this.inputRules) {
            final TRSTerm newLeftSide = this.eliminateConstants(rule.getLeft());
            final TRSTerm newRightSide = this.eliminateConstants(rule.getRight());
            assert newLeftSide instanceof TRSFunctionApplication && newRightSide instanceof TRSFunctionApplication : "Should be function applications!";
            final IGeneralizedRule newRule =
                IGeneralizedRule.create((TRSFunctionApplication) newLeftSide, newRightSide, null);
            this.transformedRules.add(newRule);
            this.history.put(newRule, rule);
        }
    }

    private TRSTerm eliminateConstants(final TRSTerm t) {
        if (t instanceof TRSVariable) {
            return t;
        } else if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            final FunctionSymbol s = f.getRootSymbol();
            if (s.getArity() == 0) {
                return TRSTerm.createFunctionApplication(
                    FunctionSymbol.create(s.getName(), 1),
                    TRSTerm.createVariable(this.fng.getFreshName("v", false)));
            } else {
                final ArrayList<TRSTerm> transformedArguments = new ArrayList<>(s.getArity());
                for (final TRSTerm arg : f.getArguments()) {
                    transformedArguments.add(this.eliminateConstants(arg));
                }
                return TRSTerm.createFunctionApplication(s, transformedArguments);
            }
        } else {
            return null;
        }
    }

    private void enumerateWays() throws AbortionException {
        // 1. Collect symbols:
        for (final IGeneralizedRule origRule : this.transformedRules) {
            this.collectSymbols(origRule.getLeft(), true);
            this.collectSymbols(origRule.getRight(), true);
        }
        this.aborter.checkAbortion();

        // 2. Enumerate the ways:
        final LinkedHashMap<FunctionSymbol, Integer> remainingPositions = new LinkedHashMap<>();
        final LinkedHashMap<FunctionSymbol, String> newNames = new LinkedHashMap<>();

        final ArrayList<FunctionSymbol> symbols = new ArrayList<>(this.symbols);
        this.generateWays(symbols, 0, remainingPositions, newNames);
    }

    private void generateWays(
        final ArrayList<FunctionSymbol> symbols,
        final int position,
        final LinkedHashMap<FunctionSymbol, Integer> remainingPositions,
        final LinkedHashMap<FunctionSymbol, String> newNames) throws AbortionException
    {
        if (position == symbols.size()) {
            this.ways.add(new Way(remainingPositions, newNames));
            this.aborter.checkAbortion();
        } else {
            final FunctionSymbol sym = symbols.get(position);
            for (int p = 0; p < sym.getArity(); p++) {
                if (this.definedSymbols.contains(sym)) {
                    newNames.put(sym, this.fng.getFreshName("f", false));
                }
                remainingPositions.put(sym, p);
                this.generateWays(symbols, position + 1, remainingPositions, newNames);
            }
        }
    }

    private void collectSymbols(final TRSTerm t, final boolean top) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            final FunctionSymbol sym = f.getRootSymbol();
            this.symbols.add(sym);
            if (top) {
                this.definedSymbols.add(sym);
            }
            for (final TRSTerm arg : f.getArguments()) {
                this.collectSymbols(arg, false);
            }
        }
    }
}
