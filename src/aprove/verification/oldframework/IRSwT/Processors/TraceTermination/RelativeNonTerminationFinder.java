package aprove.verification.oldframework.IRSwT.Processors.TraceTermination;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Finds all relatively non-terminating rules in a given trace.
 * @author Matthias Hoelzel
 */
public class RelativeNonTerminationFinder {
    /** Trace to be checked for termination. */
    private final Trace trace;

    /**
     * Maps the original rules its normalized versions.
     * Here a rule l -> r is called normlized, iff
     * l = f a x and
     * r = g b_1 b_2 b_3 ... b_k x.
     */
    private final LinkedHashMap<IGeneralizedRule, LinkedHashSet<IGeneralizedRule>> normalizedRules;

    /** Aborter: Reminds when time is running out. */
    private final Abortion aborter;

    /** Generates name which are fresh and tasty. */
    private final FreshNameGenerator fng;

    /** A fresh symbol we need to normalize variable swapping rules. */
    private final FunctionSymbol groundSymbol;

    /** Trace consisting of normalized rules. */
    private Trace normTrace;

    /**
     * True IFF we could remove at least one rule.
     */
    private boolean successful;

    /**
     * Constructor!
     * @param traceSystem input trace
     * @param abortion some aborter
     */
    public RelativeNonTerminationFinder(final Trace traceSystem, final Abortion abortion) {
        this(traceSystem, traceSystem.createFreshNameGenerator(), abortion);
    }

    /**
     * Constructor!
     * @param traceSystem input trace
     * @param gen name generator
     * @param abortion some aborter
     */
    public RelativeNonTerminationFinder(final Trace traceSystem, final FreshNameGenerator gen, final Abortion abortion)
    {
        this.trace = traceSystem;
        this.fng = gen;
        this.aborter = abortion;
        this.normalizedRules = new LinkedHashMap<>();
        this.groundSymbol = FunctionSymbol.create(this.fng.getFreshName("ground", false), 1);
        this.successful = false;
    }

    /**
     * Returns the set of relatively non-terminating rules (w.r.t. the given trace).
     * @return set of relatively non-terminating rules
     * @throws AbortionException can be aborted
     */
    public LinkedHashSet<IGeneralizedRule> findRelativelyNonTerminatingRules() throws AbortionException {
        /*
         * A rule l -> r of a finite trace R is relatively non-terminating w.r.t. R,
         * IFF one of the following conditions hold:
         * (a) l -> r is swapping and r tau ->^*_R l sigma for some substitutions tau, sigma
         * (b) l -> r is non-swapping and r ->^*_R l sigma for some substitution sigma
         * (c) some other rule l' -> r' from R satisfies (a) and we have
         *     r' tau ->^*_R l tau' -> r tau' ->^*_R l sigma for some substitutions
         *     tau, tau', sigma
         * (d) some other rule l' -> r' from R satisfies (b) and we have
         *     r' ->^*_R l tau -> r tau ->^*_R l sigma for some substitutions
         *     tau, sigma
         *
         * Since such reachability problems can be decided using the saturation
         * algorithm (a bit tinkering), we can find the relatively non-terminating rules.
         */

        // 1. Compute the normalized trace. Needed to
        //    check whether (a), (b), (c), (d) or nothing holds.
        this.computeNormalizedTraces();

        // Initialize set of already detected relatively non-terminating rule.
        // (a) or (b):
        final LinkedHashSet<IGeneralizedRule> setForAAndB = new LinkedHashSet<>();
        // (c) or (d) (but non [(a) or (b)]):
        final LinkedHashSet<IGeneralizedRule> setForCAndD = new LinkedHashSet<>();

        // 2. Find the relatively non-terminating rules, bring them all, and into the darkness bind them.
        // 2.1. Find all rules that satisfy (a) or (b):
        for (final IGeneralizedRule rule : this.trace.getRules()) {
            // Does (a) or (b) hold?
            if (this.checkReachability(rule, this.normTrace, this.swapsVariables(rule))) {
                // Yes -> Relatively Non-Terminating!
                setForAAndB.add(rule);
            }
        }

        // 2.2. Now we handle (c), (d):
        for (final IGeneralizedRule primedRule : setForAAndB) {
            // To compute the desired information we add little marks
            // at the top symbols. Then the reachability also checks that
            // the rule has been applied at least once.
            final IGeneralizedRule markedRule = this.addMarkGadgets(primedRule);
            for (final IGeneralizedRule rule : this.trace.getRules()) {
                if (setForAAndB.contains(rule)) {
                    // Does already satisfy (a) or (b), so we dont need to
                    // (c), (d).
                    continue;
                }
                final Trace markedTrace = this.computeMarkedTrace(rule);
                // Does (c) or (d) hold?
                if (this.checkReachability(markedRule, markedTrace, this.swapsVariables(primedRule))) {
                    setForCAndD.add(rule);
                }
            }
        }

        // 3. Returns relatively terminating rules:
        final LinkedHashSet<IGeneralizedRule> relativelyNonTerminating = new LinkedHashSet<>();
        relativelyNonTerminating.addAll(setForAAndB);
        relativelyNonTerminating.addAll(setForCAndD);
        for (final IGeneralizedRule originalRule : this.trace.getRules()) {
            if (!relativelyNonTerminating.contains(originalRule)) {
                this.successful = true;
            }
        }
        return relativelyNonTerminating;
    }

    public boolean wasSuccessful() {
        return this.successful;
    }

    private IGeneralizedRule addMarkGadgets(final IGeneralizedRule primedRule) {
        return this.markRule(primedRule, "1_", "0_");
    }

    private Trace computeMarkedTrace(final IGeneralizedRule rule) {
        final LinkedHashSet<IGeneralizedRule> markedRules = new LinkedHashSet<>();
        for (final IGeneralizedRule originalRule : this.trace.getRules()) {
            final boolean addMarkTransition = originalRule.equals(rule);
            for (final IGeneralizedRule normRule : this.normalizedRules.get(originalRule)) {
                markedRules.add(this.markRule(normRule, "0_", "0_"));
                markedRules.add(this.markRule(normRule, "1_", "1_"));
                if (addMarkTransition) {
                    markedRules.add(this.markRule(normRule, "0_", "1_"));
                }
            }
        }
        return new Trace(markedRules);
    }

    private IGeneralizedRule markRule(final IGeneralizedRule rule, final String leftGadget, final String rightGadget) {
        return IGeneralizedRule.create(
            this.markFunctionApplication(rule.getLeft(), leftGadget),
            this.markFunctionApplication(rule.getRight(), rightGadget),
            null);
    }

    private TRSFunctionApplication markFunctionApplication(final TRSTerm t, final String message) {
        assert t instanceof TRSFunctionApplication : "Should be function application!";
        final TRSFunctionApplication func = (TRSFunctionApplication) t;
        final FunctionSymbol sym = func.getRootSymbol();
        assert sym.getArity() == 1 : "Should have arity 1.";
        final FunctionSymbol newSymbol = FunctionSymbol.create(message + sym.getName(), sym.getArity());
        return TRSTerm.createFunctionApplication(newSymbol, func.getArgument(0));
    }

    /**
     * @throws AbortionException can be aborted
     */
    private void computeNormalizedTraces() throws AbortionException {
        final LinkedHashSet<IGeneralizedRule> normalizedRules = new LinkedHashSet<>();
        for (final IGeneralizedRule originalRule : this.trace.getRules()) {
            final LinkedHashSet<IGeneralizedRule> normRules = new LinkedHashSet<>();
            this.generateNormalizedRules(originalRule, normRules);
            this.normalizedRules.put(originalRule, normRules);
            normalizedRules.addAll(normRules);
        }

        this.normTrace = new Trace(normalizedRules);
    }

    /**
     * @param toNormalize
     * @param toComplete
     * @throws AbortionException can be aborted
     */
    private void generateNormalizedRules(
        final IGeneralizedRule toNormalize,
        final LinkedHashSet<IGeneralizedRule> toComplete) throws AbortionException
    {
        this.aborter.checkAbortion();
        if (this.hasNormalizedHeight(toNormalize)) {
            if (this.swapsVariables(toNormalize)) {
                this.normlizeSwappingRule(toNormalize, toComplete);
            } else {
                toComplete.add(toNormalize);
            }
        } else {
            if (this.hasSmallLeftSide(toNormalize)) {
                this.normalizeShortRule(toNormalize, toComplete);
            } else {
                this.shortenRule(toNormalize, toComplete);
            }
        }
    }

    /**
     * @param toNormalize
     */
    private void normlizeSwappingRule(
        final IGeneralizedRule toNormalize,
        final LinkedHashSet<IGeneralizedRule> toComplete)
    {
        final String eatingSymbolName = this.fng.getFreshName("eat", false);
        final String creatingSymbolName = this.fng.getFreshName("create", false);
        final FunctionSymbol eatingSymbol = FunctionSymbol.create(eatingSymbolName, 1);
        final FunctionSymbol creatingSymbol = FunctionSymbol.create(creatingSymbolName, 1);

        final TRSFunctionApplication leftSide = toNormalize.getLeft();
        final TRSTerm rightSideTerm = toNormalize.getRight();
        assert rightSideTerm instanceof TRSFunctionApplication : "Should be function application!";
        final TRSFunctionApplication rightSide = (TRSFunctionApplication) rightSideTerm;

        final Set<TRSVariable> leftVariables = leftSide.getVariables();
        final Set<TRSVariable> rightVariables = rightSide.getVariables();
        assert leftVariables.size() == 1 && rightVariables.size() == 1 : "Should have exactly one variable!";

        final TRSVariable leftVar = leftVariables.iterator().next();
        final TRSVariable rightVar = rightVariables.iterator().next();

        final TRSTerm leftArg = leftSide.getArgument(0);
        assert leftArg instanceof TRSFunctionApplication : "Not correctly shortened!";
        final TRSFunctionApplication leftArgFunc = (TRSFunctionApplication) leftArg;

        final TRSFunctionApplication eatenSymbol = TRSTerm.createFunctionApplication(eatingSymbol, leftVar);
        final IGeneralizedRule firstRule;
        if (leftArgFunc.getRootSymbol().equals(this.groundSymbol)) {
            firstRule =
                IGeneralizedRule.create(
                    leftSide,
                    TRSTerm.createFunctionApplication(
                        eatingSymbol,
                        TRSTerm.createFunctionApplication(this.groundSymbol, leftVar)),
                    null);
        } else {
            firstRule = IGeneralizedRule.create(leftSide, eatenSymbol, null);
        }
        toComplete.add(firstRule);

        this.createEatingRules(eatingSymbol, leftVar, eatenSymbol, toComplete);

        final TRSFunctionApplication botTerm = TRSTerm.createFunctionApplication(this.groundSymbol, leftVar);
        toComplete.add(IGeneralizedRule.create(
            TRSTerm.createFunctionApplication(eatingSymbol, botTerm),
            TRSTerm.createFunctionApplication(creatingSymbol, botTerm),
            null));

        for (final String constructor1 : this.trace.getConstructorSymbols()) {
            final FunctionSymbol constrSym1 = FunctionSymbol.create(constructor1, 1);
            this.addCreatingRules(creatingSymbol, leftVar, constrSym1, toComplete);
        }
        this.addCreatingRules(creatingSymbol, leftVar, this.groundSymbol, toComplete);

        for (final String constructor : this.trace.getConstructorSymbols()) {
            final FunctionSymbol constrSym = FunctionSymbol.create(constructor, 1);
            this.createFinalSwapRule(creatingSymbol, constrSym, rightVar, rightSide, toComplete);
        }
        this.createFinalSwapRule(creatingSymbol, this.groundSymbol, rightVar, rightSide, toComplete);
    }

    /**
     * @param creatingSymbol
     * @param constructorSymbol
     * @param rightVar
     * @param rightSide
     */
    private void createFinalSwapRule(
        final FunctionSymbol creatingSymbol,
        final FunctionSymbol constructorSymbol,
        final TRSVariable rightVar,
        final TRSFunctionApplication rightSide,
        final LinkedHashSet<IGeneralizedRule> toComplete)
    {
        final TRSFunctionApplication instantiation =
            TRSTerm.createFunctionApplication(constructorSymbol, rightVar);
        final TRSSubstitution sub = TRSSubstitution.create(rightVar, instantiation);

        final TRSFunctionApplication newLeftSide =
            TRSTerm.createFunctionApplication(creatingSymbol, instantiation);

        boolean omitInstantiation = false;
        final TRSTerm rightArg = rightSide.getArgument(0);
        if (rightArg instanceof TRSFunctionApplication && constructorSymbol.equals(this.groundSymbol)) {
            final TRSFunctionApplication rightArgFunc = (TRSFunctionApplication) rightArg;
            omitInstantiation = rightArgFunc.getRootSymbol().equals(this.groundSymbol);
        }

        final TRSFunctionApplication newRightSide;
        if (omitInstantiation) {
            newRightSide = rightSide;
        } else {
            newRightSide = rightSide.applySubstitution(sub);
        }

        final IGeneralizedRule finalRule = IGeneralizedRule.create(newLeftSide, newRightSide, null);
        toComplete.add(finalRule);
    }

    /**
     * @param eatingSymbol
     * @param leftVar
     * @param eatenSymbol
     */
    private void createEatingRules(
        final FunctionSymbol eatingSymbol,
        final TRSVariable leftVar,
        final TRSFunctionApplication eatenSymbol,

        final LinkedHashSet<IGeneralizedRule> toComplete)
    {
        for (final String constructor : this.trace.getConstructorSymbols()) {
            final FunctionSymbol constrSym = FunctionSymbol.create(constructor, 1);
            final IGeneralizedRule eatingRule =
                IGeneralizedRule.create(
                    TRSTerm.createFunctionApplication(
                        eatingSymbol,
                        TRSTerm.createFunctionApplication(constrSym, leftVar)),
                    eatenSymbol,
                    null);
            toComplete.add(eatingRule);
        }
    }

    /**
     * @param creatingSymbol
     * @param leftVar
     * @param symbol
     * @param toComplete
     */
    private void addCreatingRules(
        final FunctionSymbol creatingSymbol,
        final TRSVariable leftVar,
        final FunctionSymbol symbol,
        final LinkedHashSet<IGeneralizedRule> toComplete)
    {
        for (final String constructor2 : this.trace.getConstructorSymbols()) {
            final FunctionSymbol constrSym2 = FunctionSymbol.create(constructor2, 1);
            final TRSFunctionApplication rightSide =
                TRSTerm.createFunctionApplication(
                    creatingSymbol,
                    TRSTerm.createFunctionApplication(
                        constrSym2,
                        TRSTerm.createFunctionApplication(symbol, leftVar)));

            toComplete.add(IGeneralizedRule.create(
                TRSTerm.createFunctionApplication(
                    creatingSymbol,
                    TRSTerm.createFunctionApplication(symbol, leftVar)),
                rightSide,
                null));
        }
    }

    /**
     * @param toNormalize
     * @param toComplete
     * @throws AbortionException can be aborted
     */
    private
        void
        normalizeShortRule(final IGeneralizedRule toNormalize, final LinkedHashSet<IGeneralizedRule> toComplete)
            throws AbortionException
    {
        final TRSTerm leftArg = toNormalize.getLeft().getArgument(0);
        assert leftArg instanceof TRSVariable : "Short rule should be short!";

        final TRSVariable v = (TRSVariable) leftArg;
        final LinkedHashSet<TRSVariable> variables = new LinkedHashSet<>();
        variables.add(v);
        variables.addAll(toNormalize.getRight().getVariables());

        for (final String constr : this.trace.getConstructorSymbols()) {
            final FunctionSymbol constrSym = FunctionSymbol.create(constr, 1);
            this.addInstantiatedShortRule(toNormalize, variables, constrSym, toComplete);
            this.aborter.checkAbortion();
        }
        this.addInstantiatedShortRule(toNormalize, variables, this.groundSymbol, toComplete);
    }

    /**
     * @param toNormalize
     * @param v
     * @param sym
     * @param toComplete
     * @throws AbortionException
     */
    private void addInstantiatedShortRule(
        final IGeneralizedRule toNormalize,
        final Collection<TRSVariable> vars,
        final FunctionSymbol sym,
        final LinkedHashSet<IGeneralizedRule> toComplete) throws AbortionException
    {
        final LinkedHashMap<TRSVariable, TRSTerm> substitutionMap = new LinkedHashMap<TRSVariable, TRSTerm>();
        for (final TRSVariable v : vars) {
            substitutionMap.put(v, TRSTerm.createFunctionApplication(sym, v));
        }

        final TRSSubstitution s = TRSSubstitution.create(ImmutableCreator.create(substitutionMap));
        final IGeneralizedRule instantiatedRule =
            IGeneralizedRule.create(toNormalize.getLeft().applySubstitution(s), toNormalize
                .getRight()
                .applySubstitution(s), null);
        this.generateNormalizedRules(instantiatedRule, toComplete);
    }

    /**
     * @param toNormalize
     * @throws AbortionException
     */
    private void shortenRule(final IGeneralizedRule toNormalize, final LinkedHashSet<IGeneralizedRule> toComplete)
        throws AbortionException
    {
        // It is indeed the "straight-forward-construction"!
        final TRSFunctionApplication leftSide = toNormalize.getLeft();
        final FunctionSymbol leftRootSymbol = leftSide.getRootSymbol();

        final TRSTerm leftArgument = leftSide.getArgument(0);
        assert leftArgument instanceof TRSFunctionApplication : "Should be function application!";
        final TRSFunctionApplication leftArgFunc = (TRSFunctionApplication) leftArgument;
        final FunctionSymbol toEat = leftArgFunc.getRootSymbol();

        final TRSTerm remainingLeftPart = leftArgFunc.getArgument(0);
        final Set<TRSVariable> vars = remainingLeftPart.getVariables();

        assert vars.size() == 1 : "Expected exactly one variable!";
        final TRSVariable eliminationVariable = vars.iterator().next();

        final String newSymbolName = this.fng.getFreshName("f", false);
        final FunctionSymbol newSymbol = FunctionSymbol.create(newSymbolName, 1);
        final TRSFunctionApplication rightSideOfEatingRule =
            TRSTerm.createFunctionApplication(newSymbol, eliminationVariable);

        final TRSFunctionApplication eatTerm = TRSTerm.createFunctionApplication(toEat, eliminationVariable);
        final TRSFunctionApplication leftSideOfEatingRule =
            TRSTerm.createFunctionApplication(leftRootSymbol, eatTerm);

        final IGeneralizedRule eatingRule = IGeneralizedRule.create(leftSideOfEatingRule, rightSideOfEatingRule, null);
        toComplete.add(eatingRule);

        final TRSFunctionApplication newLeftSide =
            TRSTerm.createFunctionApplication(newSymbol, remainingLeftPart);
        final IGeneralizedRule newToNormalize = IGeneralizedRule.create(newLeftSide, toNormalize.getRight(), null);

        this.generateNormalizedRules(newToNormalize, toComplete);
    }

    /**
     * @param rule
     * @return
     */
    private boolean hasNormalizedHeight(final IGeneralizedRule rule) {
        return rule.getLeft().getSize() == 3;
    }

    /**
     * @param rule
     * @return
     */
    private boolean hasSmallLeftSide(final IGeneralizedRule rule) {
        return rule.getLeft().getSize() < 3;
    }

    /**
     * @param rule
     * @return
     */
    private boolean swapsVariables(final IGeneralizedRule rule) {
        return !rule.getLeft().getVariables().equals(rule.getRight().getVariables());
    }

    /**
     * @param rule
     * @param normalizedTrace
     * @param useRightInstantiation
     * @return
     * @throws AbortionException
     */
    private boolean checkReachability(
        final IGeneralizedRule rule,
        final Trace normalizedTrace,
        final boolean useRightInstantiation) throws AbortionException
    {
        final Pair<FiniteAutomaton, LinkedList<String>> p = this.prepareAnalysis(rule, normalizedTrace);
        final String start = p.y.pollFirst();
        if (useRightInstantiation) {
            return p.x.acceptsPrefix(start, p.y);
        } else {
            if (p.x.accepts(start, p.y)) {
                return true;
            }
            p.y.addLast(this.groundSymbol.getName());
            return p.x.accepts(start, p.y);
        }

    }

    /**
     * @param rule
     * @param normalizedTrace
     * @return
     * @throws AbortionException
     */
    private Pair<FiniteAutomaton, LinkedList<String>> prepareAnalysis(
        final IGeneralizedRule rule,
        final Trace normalizedTrace) throws AbortionException
    {
        final FiniteAutomaton fa = this.createStartingAutomaton(rule.getLeft(), normalizedTrace);
        this.saturateAutomaton(fa, normalizedTrace);

        final TRSTerm right = rule.getRight();
        final LinkedList<String> rightString = Trace.traceTermToList(right);

        return new Pair<FiniteAutomaton, LinkedList<String>>(fa, rightString);
    }

    /**
     * @param left
     * @param normalizedTrace
     * @return
     */
    private FiniteAutomaton createStartingAutomaton(final TRSFunctionApplication left, final Trace normalizedTrace) {
        final FiniteAutomaton fa = new FiniteAutomaton();
        for (final String s : normalizedTrace.getDefinedSymbols()) {
            fa.addState(s);
        }

        final LinkedList<String> strings = Trace.traceTermToList(left);
        final Iterator<String> stringIterator = strings.iterator();
        final String startState = stringIterator.next();
        String currentState = startState;
        while (stringIterator.hasNext()) {
            final String toRead = stringIterator.next();
            final String nextState = this.fng.getFreshName("state", false);
            fa.addTransition(currentState, toRead, nextState);
            currentState = nextState;
        }
        //fa.addFinalState(currentState);

        final String finalState = this.fng.getFreshName("final", false);
        fa.addFinalState(finalState);
        for (final String a : normalizedTrace.getConstructorSymbols()) {
            fa.addTransition(finalState, a, finalState);
            fa.addTransition(currentState, a, finalState);
        }
        fa.addTransition(currentState, this.groundSymbol.getName(), finalState);
        fa.addTransition(finalState, this.groundSymbol.getName(), finalState);

        return fa;
    }

    /**
     * @param fa
     * @param normalizedTrace
     * @throws AbortionException
     */
    private void saturateAutomaton(final FiniteAutomaton fa, final Trace normalizedTrace) throws AbortionException {
        boolean changed;
        do {
            this.aborter.checkAbortion();
            changed = false;
            for (final IGeneralizedRule saturationRule : normalizedTrace.getRules()) {
                final TRSTerm rightTerm = saturationRule.getRight();
                assert rightTerm instanceof TRSFunctionApplication : "Should be function application!";

                final TRSFunctionApplication rightFunc = (TRSFunctionApplication) rightTerm;
                final LinkedList<String> rightSymbols = Trace.traceTermToList(rightFunc);
                final String start = rightSymbols.pollFirst();

                final LinkedHashSet<String> reachedStates = fa.simulate(start, rightSymbols);

                final TRSFunctionApplication leftFunc = saturationRule.getLeft();
                final LinkedList<String> leftSymbols = Trace.traceTermToList(leftFunc);
                assert leftSymbols.size() == 2 : "Left side should be normalized!";

                final String startingState = leftSymbols.pollFirst();
                final String toRead = leftSymbols.pollFirst();

                for (final String reached : reachedStates) {
                    if (!fa.hasTransition(startingState, toRead, reached)) {
                        changed = true;
                        fa.addTransition(startingState, toRead, reached);
                    }
                }
            }
        } while (changed);
    }
}
