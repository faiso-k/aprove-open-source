package aprove.verification.dpframework.TRSProblem.Processors.FromITRS;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
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
public class UnneededArgumentRemover extends QTRSProcessor {
    /**
     * The proof for this processor giving information about the removed positions.
     * @author Marc Brockschmidt
     */
    private class UnneededArgumentRemoverProof extends ArgumentsRemovalProof {
        /**
         * Create a new proof.
         * @param removedArgs maps function symbols to the list of removed argument positions
         * @param names maps old function names to new ones
         */
        public UnneededArgumentRemoverProof(
                final CollectionMap<FunctionSymbol, Integer> removedArgs,
                final Map<FunctionSymbol, FunctionSymbol> names) {
            super(removedArgs, names);
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
     * Yes, we can.
     * @param qtrs any qtrs
     * @return true
     */
    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return true;
    }

    /**
     * Start working on the given qtrs.
     * @param qtrs some qtrs
     * @param aborter an aborter
     * @return a new qtrs in which positions which (more or less obviously)
     * don't influence termination were removed.
     * @param rti don't know
     * @throws AbortionException never.
     */
    @Override
    protected Result processQTRS(final QTRSProblem qtrs,
        final Abortion aborter,
        final RuntimeInformation rti)
            throws AbortionException {
        final ImmutableSet<Rule> oldRules = qtrs.getR();
        final Pair<CollectionMap<FunctionSymbol, FunctionSymbol>,
                   Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>>> p =
                       this.init(oldRules);
        final CollectionMap<FunctionSymbol, FunctionSymbol> possiblyReaching = p.x;
        final Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>> termsAtFsPositions = p.y;
        CollectionMap<FunctionSymbol, Integer> oldNeededPositions = new CollectionMap<FunctionSymbol, Integer>();
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
            for (final Rule rule : oldRules) {
                final Collection<TRSVariable> neededVarsOnRhs =
                    UnneededArgumentRemover.getNeededVariablesInFilteredTerm(rule.getRight(), newNeededPositions);
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
                        if (!arg.isVariable()) {
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
                                            newNeededPositions
                                        );
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
                    if (term instanceof TRSFunctionApplication) {
                        final FunctionSymbol fs = ((TRSFunctionApplication) term).getRootSymbol();
                        final ImmutableList<TRSTerm> args = ((TRSFunctionApplication)term).getArguments();
                        nextPos: for (int pos = 0; pos < args.size(); pos++) {
                            final TRSTerm arg = args.get(pos);
                            terms.add(arg);
                            for (final FunctionSymbol sym : arg.getFunctionSymbols()) {
                                if (possiblyReaching.contains(sym, rule.getRootSymbol())) {
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
            return ResultFactory.unsuccessful();
        }

        // Construct the result
        final Pair<QTRSProblem, Map<FunctionSymbol, FunctionSymbol>> pair =
            HelperClass.getResultingQTRS(qtrs, positionsToBeRemoved);

        final UnneededArgumentRemoverProof proof =
            new UnneededArgumentRemoverProof(positionsToBeRemoved, pair.y);

        //TODO: This is most probably complete, but that's not proven yet:
        return ResultFactory.proved(pair.x, YNMImplication.SOUND, proof);
    }


    /**
     * @param pRules set of rules
     * @param rRules another set of rules
     * @return map of function symbols to function symbols which might be
     *  reached through rewriting.
     */
    private Pair<CollectionMap<FunctionSymbol, FunctionSymbol>, Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>>> init(
            final ImmutableSet<Rule> rules) {
        final Collection<FunctionSymbol> definedSymbol =
            new LinkedHashSet<FunctionSymbol>();

        /*
         * For each defined symbol, keep a collection of terms occurring at
         * each argument position.
         */
        final Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>> termsAtFsPosition =
            new LinkedHashMap<FunctionSymbol, CollectionMap<Integer, TRSTerm>>();

        //Get all defined symbols that we might care about:
        for (final Rule rule : rules) {
            definedSymbol.add(rule.getLeft().getRootSymbol());
        }

        final CollectionMap<FunctionSymbol, FunctionSymbol> possiblyReaching =
            new CollectionMap<FunctionSymbol, FunctionSymbol>();

        //Find out what subterms exist and which defined syms are reachable:
        for (final Rule rule : rules) {
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
        final Map<FunctionSymbol, CollectionMap<Integer, TRSTerm>> termsAtFsPosition
    ) {
        CollectionMap<Integer, TRSTerm> termsAtPosition;
        final FunctionSymbol sym = fa.getRootSymbol();
        if (termsAtFsPosition.containsKey(sym)) {
            termsAtPosition = termsAtFsPosition.get(sym);
        } else {
            termsAtPosition = new CollectionMap<Integer, TRSTerm>();
        }
        for (int i = 0; i < sym.getArity(); i++) {
            termsAtPosition.add(i, fa.getArgument(i).getStandardRenumbered());
        }
        termsAtFsPosition.put(sym, termsAtPosition);
    }

    private static Collection<TRSVariable> getNeededVariablesInFilteredTerm(
        final TRSTerm t,
        final CollectionMap<FunctionSymbol, Integer> keptPositions
    ) {
        if (t.isVariable()) {
            return Collections.singleton((TRSVariable) t);
        }
        final Collection<TRSVariable> neededVars = new LinkedHashSet<TRSVariable>();
        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
        final ImmutableList<TRSTerm> args = fa.getArguments();
        final Collection<Integer> keptFaPositions = keptPositions.getNotNull(fa.getRootSymbol());
        for (int faPos = 0; faPos < args.size(); faPos++) {
            if (keptFaPositions.contains(faPos)) {
                neededVars.addAll(UnneededArgumentRemover.getNeededVariablesInFilteredTerm(args.get(faPos), keptPositions));
            }
        }
        return neededVars;
    }

}
