package aprove.verification.oldframework.WeightedIntTrs;

import java.util.*;

import aprove.Globals;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Removes arguments from terms. Believes that they are not important for termination.
 *
 * @author Marc Brockschmidt
 */
public class WeightedIntTrsUnneededArgumentFilterProcessor extends WeightedIntTrsArgumentFilter {

    @ParamsViaArgumentObject
    public WeightedIntTrsUnneededArgumentFilterProcessor(Arguments args) {
        super(args);
    }
    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        return processInternal((AbstractWeightedIntTermSystem<?>) obl);
    }

    private <T extends AbstractWeightedIntRule<T>> Result processInternal(AbstractWeightedIntTermSystem<T> obl) throws AbortionException {

        final Pair<Pair<Set<T>, Map<FunctionSymbol, FunctionSymbol>>, CollectionMap<FunctionSymbol, Integer>> r =
            processRules(obl.getRules(), false);

        if (r != null) {
            final TRSFunctionApplication newStartTerm;
            if (obl.getStartTerm() != null) {
                newStartTerm =
                    (TRSFunctionApplication) HelperClass.remove(
                        obl.getStartTerm(),
                        r.y,
                        r.x.y,
                        r.y.keySet(),
                        IDPPredefinedMap.DEFAULT_MAP);
            } else {
                newStartTerm = null;
            }
            if (args.propagateLowerBounds()) {
                return ResultFactory.proved(
                        obl.copyWithNewRules(r.x.x, newStartTerm),
                        SoundUpperUnsoundLowerBound.forConcreteBounds(),
                        new WeightedIntTrsUnneededArgumentFilterProof(ArgumentsRemovalProof.getFilterRules(r.y, r.x.y)));
            } else {
                return ResultFactory.proved(
                    obl.copyWithNewRules(r.x.x, newStartTerm),
                    UpperBound.forConcreteBounds(),
                    new WeightedIntTrsUnneededArgumentFilterProof(ArgumentsRemovalProof.getFilterRules(r.y, r.x.y)));
            }
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    /**
     * @param rules some set of rules
     * @param allowOverapproximation Whether transformations that destroy the completeness of the proof may be performed
     * @return a pair of filtered rules and a mapping detailing which positions are to be filtered
     */
    public static <T extends AbstractWeightedIntRule<T>> WeightedArgumentFilterResult<T> processRules(final Set<T> rules, boolean allowOverapproximation) {
        return processRules(rules, Collections.emptySet(), allowOverapproximation);
    }

    /**
     * @param rules some set of rules
     * @param protectedSymbols TODO document me
     * @param allowOverapproximation Whether transformations that destroy the completeness of the proof may be performed
     * @return a pair of filtered rules and a mapping detailing which positions are to be filtered
     */
    public static <T extends AbstractWeightedIntRule<T>> WeightedArgumentFilterResult<T> processRules(
        Set<T> rules,
        Set<FunctionSymbol> protectedSymbols,
        boolean allowOverapproximation
    ) {
        final Pair<CollectionMap<FunctionSymbol, FunctionSymbol>, Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>>> p =
            init(rules);
        final CollectionMap<FunctionSymbol, FunctionSymbol> possiblyReaching = p.x;
        final Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>> termsAtFsPositions = p.y;

        CollectionMap<FunctionSymbol, Integer> oldNeededPositions = new CollectionMap<>();

        boolean changed;
        do {
            changed = false;

            //Copy over old filter:
            final CollectionMap<FunctionSymbol, Integer> newNeededPositions =
                new CollectionMap<>();
            for (final Map.Entry<FunctionSymbol, Collection<Integer>> e : oldNeededPositions.entrySet()) {
                newNeededPositions.put(e.getKey(), new LinkedHashSet<>(e.getValue()));
            }
            /* Collect, for each function symbol in all rules, positions which
             * could somehow influence termination */
            for (final T rule : rules) {
                final Collection<TRSVariable> neededVars = new HashSet<>();
                for (TRSTerm t : rule.getRight()) {
                    neededVars.addAll(getNeededVariablesInFilteredTerm(t, newNeededPositions));
                }
                if (rule.getCondition() != null) {
                    neededVars.addAll(rule.getCondition().getVariables());
                }
                final LinkedList<TRSFunctionApplication> lhsSubTermsToCheck = new LinkedList<>();
                lhsSubTermsToCheck.add(rule.getLeft());
                while (!lhsSubTermsToCheck.isEmpty()) {
                    final TRSFunctionApplication fa = lhsSubTermsToCheck.pop();
                    final FunctionSymbol fs = fa.getRootSymbol();
                    final ImmutableList<TRSTerm> faArgs = fa.getArguments();
                    for (int pos = 0; pos < faArgs.size(); pos++) {
                        final TRSTerm arg = faArgs.get(pos);
                        if (!arg.isVariable()) {
                            lhsSubTermsToCheck.add((TRSFunctionApplication) arg);
                        }
                        //(i): non-variable:
                        if (!arg.isVariable()) {
                            final TRSFunctionApplication argFa = (TRSFunctionApplication) arg;
                            //Binds variables on the right, we need it:
                            final Set<TRSVariable> boundVars = argFa.getVariables();
                            boundVars.retainAll(neededVars);
                            if (boundVars.size() > 0) {
                                if (newNeededPositions.add(fs, pos)) {
                                    changed = true;
                                }
                            } else {
                                if (termsAtFsPositions.get(fs).get(pos).size() != 1) {
                                    if (newNeededPositions.add(fs, pos)) {
                                        changed = true;
                                    }
                                } else {
                                    //We don't need ya, you're always the same!
                                }
                            }
                        } else {
                            //progagation of needed vars from the rhs
                            if (neededVars.contains(arg)) {
                                changed |= newNeededPositions.add(fs, pos);
                            } else {
                                /* (ii): non-linear positions:
                                 * lhsArgs.get(pos) is a variable - check if there is another positions
                                 * where it appears.
                                 */
                                for (int otherPos = 0; otherPos < faArgs.size(); otherPos++) {
                                    final Collection<TRSVariable> otherPosVariables =
                                        WeightedIntTrsUnneededArgumentFilterProcessor.getNeededVariablesInFilteredTerm(faArgs.get(otherPos), newNeededPositions);
                                    if (pos != otherPos && otherPosVariables.contains(arg)) {
                                        changed |= newNeededPositions.add(fs, pos);
                                        changed |= newNeededPositions.add(fs, otherPos);
                                    }
                                }
                            }
                        }
                    }
                }

                //(iii): possible recursive positions and conditions:
                final Queue<TRSTerm> terms = new LinkedList<>();
                terms.addAll(rule.getRight());
                while (!terms.isEmpty()) {
                    final TRSTerm term = terms.poll();
                    if (term instanceof TRSFunctionApplication
                        && !IDPPredefinedMap.DEFAULT_MAP.isPredefined(((TRSFunctionApplication) term).getRootSymbol())
                        && !(((TRSFunctionApplication) term).getRootSymbol())
                            .equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL))
                    {
                        final FunctionSymbol fs = ((TRSFunctionApplication) term).getRootSymbol();
                        final ImmutableList<TRSTerm> args = ((TRSFunctionApplication) term).getArguments();
                        nextPos: for (int pos = 0; pos < args.size(); pos++) {
                            final TRSTerm arg = args.get(pos);
                            terms.add(arg);
                            for (final FunctionSymbol sym : arg.getFunctionSymbols()) {
                                if (WeightedIntTrsUnneededArgumentFilterProcessor.isPredefinedRelation(sym)) {
                                    if (newNeededPositions.add(fs, pos)) {
                                        changed = true;
                                    }
                                    continue nextPos;
                                } else if (possiblyReaching.contains(sym, rule.getRootSymbol())) {
                                    changed |= newNeededPositions.add(fs, pos);
                                    continue nextPos;
                                }
                            }
                        }
                    }
                }
            }
            oldNeededPositions = newNeededPositions;
        } while (changed);
        // For every defined symbol mark the positions that can be deleted:
        final CollectionMap<FunctionSymbol, Integer> positionsToBeRemoved =
            new CollectionMap<>();
        boolean removedAnything = false;
        for (final Map.Entry<FunctionSymbol, Collection<Integer>> e : oldNeededPositions.entrySet()) {
            final FunctionSymbol fs = e.getKey();
            if (IDPPredefinedMap.DEFAULT_MAP.isPredefined(fs)
                || fs.equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL))
            {
                continue;
            }
            final Collection<Integer> neededPositions = e.getValue();
            for (int i = 0; i < fs.getArity(); i++) {
                if (!neededPositions.contains(i)) {
                    positionsToBeRemoved.add(fs, i);
                    removedAnything = true;
                }
            }
        }

        //Do not filter in certain symbols:
        for (final FunctionSymbol protectedSym : protectedSymbols) {
            positionsToBeRemoved.remove(protectedSym);
        }

        if (!allowOverapproximation) {
            for (final T rule : rules) {
                dontRemovePositionsNeededForNeededConditions(rule, rule.getCondition(), positionsToBeRemoved, IDPPredefinedMap.DEFAULT_MAP);
            }
        }

        if (!removedAnything) {
            // No argument can be removed
            return null;
        }

        // Construct the result
        final Pair<Set<T>, Map<FunctionSymbol, FunctionSymbol>> newRulePair =
            WeightedIntTrsArgumentFilter.getResultingRules(rules, positionsToBeRemoved, new LinkedHashSet<FunctionSymbol>());

        return new WeightedArgumentFilterResult<>(newRulePair, positionsToBeRemoved);
    }

    /**
     * Make sure that no variables that are needed for a condition in which a needed variable
     * occurs, are removed. E.g. if there variable <code>x1</code> should not be removed and
     * there is a condition <code>x1 = x2 + 3</code>, then <code>x2</code> must not removed
     * as well, since otherwise the condition would be dropped
     *
     * @param rule The rule for which all needed arguments should be retained
     * @param condTerm The condition term of the rule to check.
     * Pass the condition of the rule initially
     * @param positionsToBeRemoved The positions to be removed. This will be modified as new
     * positions are detected that must not be removed
     * @param predefinedMap A map that specifies the predefined function symbols
     * @return Whether or not <code>positionsToBeRemoved</code> was modified
     */
    private static <T extends AbstractWeightedIntRule<T>> boolean dontRemovePositionsNeededForNeededConditions(T rule, TRSTerm condTerm, CollectionMap<FunctionSymbol, Integer> positionsToBeRemoved, IDPPredefinedMap predefinedMap) {
        // If there is no condTerm there is nothing to do
        if (condTerm == null) {
            return false;
        }


        // If the term is a conjunction or disjunction, inspect each subterm individually
        if (condTerm instanceof TRSFunctionApplication) {
            TRSFunctionApplication funcApplTerm = (TRSFunctionApplication) condTerm;
            if (predefinedMap.isLand(funcApplTerm.getFunctionSymbol()) || predefinedMap.isLor(funcApplTerm.getFunctionSymbol())) {
                if (Globals.useAssertions) {
                    assert funcApplTerm.getFunctionSymbol().getArity() == 2;
                }
                boolean changed = false;
                boolean changedInLastIteration = false;
                do {
                    changedInLastIteration = false;
                    changedInLastIteration |= dontRemovePositionsNeededForNeededConditions(rule, funcApplTerm.getArgument(0), positionsToBeRemoved, predefinedMap);
                    changedInLastIteration |= dontRemovePositionsNeededForNeededConditions(rule, funcApplTerm.getArgument(1), positionsToBeRemoved, predefinedMap);
                    changed |= changedInLastIteration;
                } while (changedInLastIteration);
                return changed;
            }
        }

        // If the term is not a disjunction or conjunction consider it as whole

        Set<TRSFunctionApplication> funcAppls = new LinkedHashSet<>();
        funcAppls.add(rule.getLeft());
        funcAppls.addAll(rule.getRight());

        // Gather all variables that shall not be removed
        Set<TRSVariable> neededVars = new LinkedHashSet<>();
        for (TRSFunctionApplication funcAppl : funcAppls) {
            for (int i = 0; i < funcAppl.getFunctionSymbol().getArity(); i++) {
                Collection<Integer> positionsToBeRemovedInThisFuncAppl = positionsToBeRemoved.get(funcAppl.getFunctionSymbol());
                if (positionsToBeRemovedInThisFuncAppl != null && !positionsToBeRemovedInThisFuncAppl.contains(i)) {
                    neededVars.addAll(funcAppl.getArgument(i).getVariables());
                }
            }
        }

        boolean changed = false;
        boolean changedInLastIteration;

        do {
            changedInLastIteration = false;

            // Since the sets must not be modified while iterating, gather all changes
            // and apply them after iterating
            Set<TRSVariable> newNeededVars = new LinkedHashSet<>();
            Set<Pair<FunctionSymbol, Integer>> dontRemove = new LinkedHashSet<>();

            for (TRSVariable var : neededVars) {
                if (condTerm.getVariables().contains(var)) {
                    // condTerm is needed. Add all other variables in the term are needed too

                    // Don't do anything if all variables in the condTerm are already
                    // in neededVars
                    if (!neededVars.containsAll(condTerm.getVariables())) {
                        newNeededVars.addAll(condTerm.getVariables());

                        for (TRSFunctionApplication funcAppl : funcAppls) {
                            if (positionsToBeRemoved.get(funcAppl.getFunctionSymbol()) != null) {
                                for (Integer pos : positionsToBeRemoved.get(funcAppl.getFunctionSymbol())) {
                                    if (!Collections.disjoint(funcAppl.getArgument(pos).getVariables(), condTerm.getVariables())) {
                                        // The variable at pos occurs in the condTerm. Don't remove pos
                                        changedInLastIteration = true;
                                        dontRemove.add(new Pair<>(funcAppl.getFunctionSymbol(), pos));
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Apply changes
            for (Pair<FunctionSymbol, Integer> pair : dontRemove) {
                positionsToBeRemoved.removeFromCollection(pair.x, pair.y);
            }
            neededVars.addAll(newNeededVars);

            changed |= changedInLastIteration;
        } while (changedInLastIteration);

        return changed;
    }

    /**
     * @param rules set of rules
     * @return a pair:
     *  first element gives an approximation of the DP graph (i.e., it maps a function symbol to the
     *   defined symbols that are reachable)
     *  second element gives for each function symbol all terms occurring as a certain argument
     */
    private static <T extends AbstractWeightedIntRule<T>>
        Pair<CollectionMap<FunctionSymbol, FunctionSymbol>, Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>>>
        init(final Set<T> rules)
    {
        final Collection<FunctionSymbol> definedSymbols = new LinkedHashSet<>();

        /*
         * For each defined symbol, keep a collection of terms occurring at
         * each argument position.
         */
        final Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>> termsAtFsPosition =
            new LinkedHashMap<>();

        //Get all defined symbols that we might care about:
        for (final T rule : rules) {
            definedSymbols.add(rule.getLeft().getRootSymbol());
        }

        final CollectionMap<FunctionSymbol, FunctionSymbol> possiblyReaching =
            new CollectionMap<>();

        //Find out what subterms exist and which defined syms are reachable:
        for (final T rule : rules) {
            for (final TRSTerm t : rule.getLeft().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    WeightedIntTrsUnneededArgumentFilterProcessor.noteTermsForFS(fa, termsAtFsPosition);
                }
            }

            for (final TRSFunctionApplication foo : rule.getRight()) {
                for (final TRSTerm t : foo.getSubTerms()) {
                    if (t instanceof TRSFunctionApplication) {
                        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                        final FunctionSymbol sym = fa.getRootSymbol();

                        WeightedIntTrsUnneededArgumentFilterProcessor.noteTermsForFS(fa, termsAtFsPosition);
                        if (definedSymbols.contains(sym)) {
                            possiblyReaching.add(rule.getRootSymbol(), sym);
                        }
                    }
                }
            }
        }

        //Now approximate the DP graph _really_ badly:
        boolean changed;
        do {
            changed = false;
            for (final Map.Entry<FunctionSymbol, Collection<FunctionSymbol>> e : possiblyReaching.entrySet()) {
                final Collection<FunctionSymbol> indirectlyReachable = new LinkedHashSet<>();
                for (final FunctionSymbol reachedSym : e.getValue()) {
                    indirectlyReachable.addAll(possiblyReaching.getNotNull(reachedSym));
                }
                if (e.getValue().addAll(indirectlyReachable)) {
                    changed = true;
                }
            }
        } while (changed);

        return new Pair<>(
            possiblyReaching,
            termsAtFsPosition);
    }

    /**
     * @param fa some function application
     * @param termsAtFsPosition a map in which we enter the terms occurring as arguments of <code>fa</code>
     */
    @SuppressWarnings("boxing")
    private static void noteTermsForFS(
        final TRSFunctionApplication fa,
        final Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>> termsAtFsPosition)
    {
        CollectionMap<Integer, TRSTerm> termsAtPosition;
        final FunctionSymbol sym = fa.getRootSymbol();
        if (termsAtFsPosition.containsKey(sym)) {
            termsAtPosition = termsAtFsPosition.get(sym);
        } else {
            termsAtPosition = new CollectionMap<>();
        }

        for (int i = 0; i < sym.getArity(); i++) {
            termsAtPosition.add(i, fa.getArgument(i).getStandardRenumbered());
        }

        termsAtFsPosition.put(sym, termsAtPosition);
    }

    /**
     * @param t some Term
     * @param keptPositions the positions which we are planning to keep. Everything else is ignored.
     * @return a set of variables occurring on positions we want to keep.
     */
    @SuppressWarnings("boxing")
    private static Collection<TRSVariable> getNeededVariablesInFilteredTerm(
        final TRSTerm t,
        final CollectionMap<FunctionSymbol, Integer> keptPositions
    ) {
        if (t.isVariable()) {
            return Collections.singleton((TRSVariable) t);
        }
        final Collection<TRSVariable> neededVars = new LinkedHashSet<>();
        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
        final ImmutableList<TRSTerm> args = fa.getArguments();
        final Collection<Integer> keptFaPositions = keptPositions.getNotNull(fa.getRootSymbol());
        for (int faPos = 0; faPos < args.size(); faPos++) {
            if (keptFaPositions.contains(faPos)
                || IDPPredefinedMap.DEFAULT_MAP.isPredefined(fa.getRootSymbol())
                || fa.getRootSymbol().equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL))
            {
                neededVars.addAll(WeightedIntTrsUnneededArgumentFilterProcessor.getNeededVariablesInFilteredTerm(args.get(faPos), keptPositions));
            }
        }
        return neededVars;
    }

    /**
     * @param fs some function symbol
     * @return true if this symbol has a predefined semantics
     */
    private static boolean isPredefinedRelation(final FunctionSymbol fs) {
        final IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        return
            predefinedMap.isEq(fs)
            || predefinedMap.isNeq(fs)
            || predefinedMap.isGe(fs)
            || predefinedMap.isGt(fs)
            || predefinedMap.isLe(fs)
            || predefinedMap.isLt(fs);
    }

    /**
     * The proof for this processor giving information about the removed positions.
     * @author Marc Brockschmidt
     */
    private static class WeightedIntTrsUnneededArgumentFilterProof extends DefaultProof {
        /**
         * The arguments that are removed.
         */
        private final Collection<Rule> rem;

        /**
         * Create a new proof.
         * @param removedArgs maps function symbols to the list of removed argument positions
         */
        public WeightedIntTrsUnneededArgumentFilterProof(final Collection<Rule> removedArgs) {
            this.rem = removedArgs;
        }

        /**
         * @return the proof as a nice string representation.
         * @param o an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Some arguments are removed because they cannot influence termination. ");
            sb.append("We removed arguments according to the following replacements:");
            sb.append(o.linebreak());
            sb.append(o.set(this.rem, Export_Util.RULES));
            return sb.toString();
        }
    }
}
