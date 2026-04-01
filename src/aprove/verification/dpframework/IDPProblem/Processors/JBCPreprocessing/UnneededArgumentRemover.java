package aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This processor removes arguments that can't influence termination.
 * TODO: There's a TeXed proof and a complete explanation for this around, but
 * the URI to that is not stable yet.
 *
 * @author Marc Brockschmidt
 */
public class UnneededArgumentRemover extends ITRSProcessor {
    /**
     * Convenience class holding arguments passed in from the strategy.
     */
    public static class Arguments {
        /**
         * If true, try to consider only integers and ignore all other
         * constructor symbols on the lhs. This makes this proof incomplete.
         */
        public boolean onlyConsiderIntegers = false;
    }

    /**
     * The proof for this processor giving information about the removed positions.
     * @author Marc Brockschmidt
     */
    private class UnneededArgumentRemoverProof extends ArgumentsRemovalProof {
        /**
         * Create a new proof.
         * @param itrsProblem the ITRSProblem that has been processed
         * @param removedArgs maps function symbols to the list of removed argument positions
         */
        public UnneededArgumentRemoverProof(
                final ITRSProblem itrsProblem,
                final Collection<Rule> removedArgs) {
            super(itrsProblem, removedArgs);
        }

        /**
         * @return the proof as a nice string representation.
         * @param eu an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb =
                new StringBuilder(
                    "Some arguments are removed because they cannot influence termination.");
            sb.append(eu.linebreak());
            super.export(eu, sb);
            return sb.toString();
        }
    }

    /**
     * If true, try to consider only integers and ignore all other
     * constructor symbols on the lhs. This makes this proof incomplete.
     */
    private final boolean onlyConsiderIntegers;

    /**
     * Create a new processor instance.
     * @param arguments object holding parameters for this processor
     */
    @ParamsViaArgumentObject
    public UnneededArgumentRemover(final Arguments arguments) {
        this.onlyConsiderIntegers = arguments.onlyConsiderIntegers;
    }


    public UnneededArgumentRemover() {
        this.onlyConsiderIntegers = false;
    }

    /**
     * Yes, we can.
     * @param itrs any itrs
     * @return true
     */
    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return true;
    }

    /**
     * @param pRules set of rules
     * @param rRules another set of rules
     * @return map of function symbols to function symbols which might be
     *  reached through rewriting.
     */
    private Pair<CollectionMap<FunctionSymbol, FunctionSymbol>, Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>>> init(
            final Set<GeneralizedRule> pRules,
            final Set<GeneralizedRule> rRules) {
        final Collection<FunctionSymbol> definedSymbol =
            new LinkedHashSet<FunctionSymbol>();

        /*
         * For each defined symbol, keep a collection of terms occurring at
         * each argument position.
         */
        final Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>> termsAtFsPosition =
            new LinkedHashMap<FunctionSymbol, CollectionMap<Integer, TRSTerm>>();

        //Get all defined symbols that we might care about:
        for (final GeneralizedRule rule : pRules) {
            definedSymbol.add(rule.getLeft().getRootSymbol());
        }
        for (final GeneralizedRule rule : rRules) {
            definedSymbol.add(rule.getLeft().getRootSymbol());
        }

        final CollectionMap<FunctionSymbol, FunctionSymbol> possiblyReaching =
            new CollectionMap<FunctionSymbol, FunctionSymbol>();

        //Find out what subterms exist and which defined syms are reachable:
        for (final GeneralizedRule rule : pRules) {
            for (final TRSTerm t : rule.getLeft().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    UnneededArgumentRemover.noteTermsForFS(fa, termsAtFsPosition);
                }
            }

            for (final TRSTerm t : rule.getRight().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    final FunctionSymbol sym = fa.getRootSymbol();

                    UnneededArgumentRemover.noteTermsForFS(fa, termsAtFsPosition);
                    if (definedSymbol.contains(sym)) {
                        possiblyReaching.add(rule.getRootSymbol(), sym);
                    }
                }
            }
        }
        for (final GeneralizedRule rule : rRules) {
            for (final TRSTerm t : rule.getLeft().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    UnneededArgumentRemover.noteTermsForFS(fa, termsAtFsPosition);
                }
            }

            for (final TRSTerm t : rule.getRight().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    final FunctionSymbol sym = fa.getRootSymbol();

                    UnneededArgumentRemover.noteTermsForFS(fa, termsAtFsPosition);
                    if (definedSymbol.contains(sym)) {
                        possiblyReaching.add(rule.getRootSymbol(), sym);
                    }
                }
            }
        }

        //Now approximate the DP graph _really_ badly:
        boolean changed;
        do {
            changed = false;
            for (final Map.Entry<FunctionSymbol, Collection<FunctionSymbol>> e : possiblyReaching.entrySet()) {
                final Collection<FunctionSymbol> indirectlyReachable = new LinkedHashSet<FunctionSymbol>();
                for (final FunctionSymbol reachedSym : e.getValue()) {
                    indirectlyReachable.addAll(possiblyReaching.getNotNull(reachedSym));
                }
                if (e.getValue().addAll(indirectlyReachable)) {
                    changed = true;
                }
            }
        } while (changed);

        return new Pair<CollectionMap<FunctionSymbol, FunctionSymbol>,
                        Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>>>(
                                possiblyReaching,
                                termsAtFsPosition);
    }

    private static void noteTermsForFS(
            final TRSFunctionApplication fa,
            final Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>> termsAtFsPosition) {
        CollectionMap<Integer, TRSTerm> termsAtPosition;
        final FunctionSymbol sym = fa.getRootSymbol();
        if (termsAtFsPosition.containsKey(sym)) {
            termsAtPosition = termsAtFsPosition.get(sym);
        } else {
            termsAtPosition =
                new CollectionMap<Integer, TRSTerm>();
        }

        for (int i = 0; i < sym.getArity(); i++) {
            termsAtPosition.add(i, fa.getArgument(i).getStandardRenumbered());
        }
        termsAtFsPosition.put(sym, termsAtPosition);
    }

    private static Collection<TRSVariable> getNeededVariablesInFilteredTerm(
        final TRSTerm t,
        final CollectionMap<FunctionSymbol, Integer> keptPositions,
        final IDPPredefinedMap predefinedMap
    ) {
        if (t.isVariable()) {
            return Collections.singleton((TRSVariable) t);
        }
        final Collection<TRSVariable> neededVars = new LinkedHashSet<TRSVariable>();
        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
        final ImmutableList<TRSTerm> args = fa.getArguments();
        final Collection<Integer> keptFaPositions = keptPositions.getNotNull(fa.getRootSymbol());
        for (int faPos = 0; faPos < args.size(); faPos++) {
            if (
                keptFaPositions.contains(faPos)
                || predefinedMap.isPredefined(fa.getRootSymbol())
                || fa.getRootSymbol().equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL)
            ) {
                neededVars.addAll(UnneededArgumentRemover.getNeededVariablesInFilteredTerm(args.get(faPos), keptPositions, predefinedMap));
            }
        }
        return neededVars;
    }

    private static boolean isPredefinedRelation(final FunctionSymbol fs, final IDPPredefinedMap predefinedMap) {
        return predefinedMap.isEq(fs)
            || predefinedMap.isNeq(fs)
            || predefinedMap.isGe(fs)
            || predefinedMap.isGt(fs)
            || predefinedMap.isLe(fs)
            || predefinedMap.isLt(fs);
    }

    public Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
           Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
           Collection<Rule>> processRulePair(
            final Set<GeneralizedRule> pRules,
            final Set<GeneralizedRule> rRules,
            final IDPPredefinedMap predefinedMap) {

        final Pair<CollectionMap<FunctionSymbol, FunctionSymbol>,
             Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>>> p = this.init(pRules, rRules);
        final CollectionMap<FunctionSymbol, FunctionSymbol> possiblyReaching = p.x;
        final Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>> termsAtFsPositions = p.y;

        final Collection<GeneralizedRule> combinedRules =
            new LinkedHashSet<GeneralizedRule>(pRules);
        if (rRules != null) {
            combinedRules.addAll(rRules);
        }

        CollectionMap<FunctionSymbol, Integer> oldNeededPositions =
            new CollectionMap<FunctionSymbol, Integer>();

        boolean changed;
        do {
            changed = false;

            //Copy over old filter:
            final CollectionMap<FunctionSymbol, Integer> newNeededPositions =
                new CollectionMap<FunctionSymbol, Integer>();
            for (final Map.Entry<FunctionSymbol, Collection<Integer>> e : oldNeededPositions.entrySet()) {
                newNeededPositions.put(e.getKey(), new LinkedHashSet<Integer>(e.getValue()));
            }

            /* Collect, for each function symbol in all rules, positions which
             * could somehow influence termination */
            for (final GeneralizedRule rule : combinedRules) {
                final Collection<TRSVariable> neededVarsOnRhs =
                    UnneededArgumentRemover.getNeededVariablesInFilteredTerm(
                        rule.getRight(),
                        newNeededPositions,
                        predefinedMap
                    );
                final Stack<TRSFunctionApplication> lhsSubTermsToCheck = new Stack<TRSFunctionApplication>();
                lhsSubTermsToCheck.add(rule.getLeft());
                while (!lhsSubTermsToCheck.empty()) {
                    final TRSFunctionApplication fa = lhsSubTermsToCheck.pop();
                    final FunctionSymbol fs = fa.getRootSymbol();
                    final ImmutableList<TRSTerm> faArgs = fa.getArguments();
                    for (int pos = 0; pos < faArgs.size(); pos++) {
                        final TRSTerm arg = faArgs.get(pos);
                        if (!arg.isVariable()) {
                            lhsSubTermsToCheck.add((TRSFunctionApplication) arg);
                        }
                        //(i): non-variable:
                        if (!this.onlyConsiderIntegers && !arg.isVariable()) {
                            final TRSFunctionApplication argFa = (TRSFunctionApplication) arg;
                            //Binds variables on the right, we need it:
                            final Set<TRSVariable> boundVars = argFa.getVariables();
                            boundVars.retainAll(neededVarsOnRhs);
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

                        } else if (this.onlyConsiderIntegers) {
                            if (arg.equals(PredefinedSemanticsFactory.BOOLEAN_TERM_TRUE)
                                    || arg.equals(PredefinedSemanticsFactory.BOOLEAN_TERM_FALSE)) {
                                changed |= newNeededPositions.add(fs, pos);
                            }
                        } else {
                            //progagation of needed vars from the rhs
                            if (neededVarsOnRhs.contains(arg)) {
                                changed |= newNeededPositions.add(fs, pos);
                            } else {
                                /* (ii): non-linear positions:
                                 * lhsArgs.get(pos) is a variable - check if there is another positions
                                 * where it appears.
                                 */
                                for (int otherPos = 0; otherPos < faArgs.size(); otherPos++) {
                                    final Collection<TRSVariable> otherPosVariables =
                                        UnneededArgumentRemover.getNeededVariablesInFilteredTerm(
                                                faArgs.get(otherPos),
                                                newNeededPositions,
                                                predefinedMap);
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
                final Queue<TRSTerm> terms = new LinkedList<TRSTerm>();
                terms.add(rule.getRight());
                while (!terms.isEmpty()) {
                    final TRSTerm term = terms.poll();
                    if (
                        term instanceof TRSFunctionApplication
                        && !predefinedMap.isPredefined(((TRSFunctionApplication) term).getRootSymbol())
                        && !(
                            ((TRSFunctionApplication)term).getRootSymbol()
                        ).equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL)
                    ) {
                        final FunctionSymbol fs = ((TRSFunctionApplication) term).getRootSymbol();
                        final ImmutableList<TRSTerm> args = ((TRSFunctionApplication) term).getArguments();
                        nextPos: for (int pos = 0; pos < args.size(); pos++) {
                            final TRSTerm arg = args.get(pos);
                            terms.add(arg);
                            for (final FunctionSymbol sym : arg.getFunctionSymbols()) {
                                if (UnneededArgumentRemover.isPredefinedRelation(sym, predefinedMap)) {
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
            new CollectionMap<FunctionSymbol, Integer>();
        boolean removedAnything = false;
        for (final Map.Entry<FunctionSymbol, Collection<Integer>> e : oldNeededPositions.entrySet()) {
            final FunctionSymbol fs = e.getKey();
            if (predefinedMap.isPredefined(fs)
                    || fs.equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL)) {
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

        if (!removedAnything) {
            // No argument can be removed
            return null;
        }

        // Construct the result
        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newRPair =
            HelperClass.getResultingRules(rRules, predefinedMap, positionsToBeRemoved, new LinkedHashSet<FunctionSymbol>());

        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newPPair =
            HelperClass.getResultingRules(pRules, predefinedMap, positionsToBeRemoved, new LinkedHashSet<FunctionSymbol>());

        return new Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                          Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                          Collection<Rule>>(newPPair, newRPair,  ArgumentsRemovalProof.getFilterRules(positionsToBeRemoved, newPPair.y));
    }

    /**
     * Start working on the given ITRS.
     * @param itrs some itrs
     * @param aborter an aborter
     * @return the ITRS with unneeded arguments removed (together with a proof
     * and such)
     * @throws AbortionException never.
     */
    @Override
    protected Result processITRSProblem(final ITRSProblem itrs, final Abortion aborter)
    throws AbortionException {
        final Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                     Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                     Collection<Rule>>
        resultTriple =
            this.processRulePair(Collections.EMPTY_SET, itrs.getR(), itrs.getPredefinedMap());

        if (resultTriple == null) {
            // No argument can be removed
            return ResultFactory.unsuccessful();
        }

        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newRulesPair = resultTriple.y;
        final Set<GeneralizedRule> newRules = newRulesPair.x;
        final Collection<Rule> positionsToBeRemoved = resultTriple.z;


        final IQTermSet newQ = new IQTermSet(HelperClass.getNewQ(newRules), itrs.getPredefinedMap());
        final ITRSProblem newItrs = ITRSProblem.create(newRules, newQ);


        final UnneededArgumentRemoverProof proof =
            new UnneededArgumentRemoverProof(itrs, positionsToBeRemoved);

        //TODO: This is most probably complete, but that's not proven yet:
        return ResultFactory.proved(newItrs, YNMImplication.SOUND, proof);
    }

}
