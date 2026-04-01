package aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This processor removes ground terms that appear inside every occurrence of
 * some function application without being changed.
 *
 * <pre>
 * f(x, y, 0, NIL) -&gt; ...
 * ... -&gt; f(x, y, z, NIL)
 * ... -&gt; f(x, y, 0, NIL)
 * results in
 * f(x, y, 0) -&gt; ...
 * ... -&gt; f(x, y, z)
 * ... -&gt; f(x, y, 0)
 * </pre>
 * @author cotto, Christian von Essen
 */
public class GroundTermRemover extends ITRSProcessor {

    /**
     * The proof for this processor giving information about the ground terms
     * and how they are removed.
     * @author cotto
     */
    private class GroundTermsRemoverProof extends ArgumentsRemovalProof {
        /**
         * The ground terms that were removed.
         */
        //private final Collection<Term> groundTerms;

        /**
         * Create a new proof.
         * @param removedArgsRules information about removed arguments.
         */
        public GroundTermsRemoverProof(
                final ITRSProblem itrsProblem,
                final Collection<Rule> removedArgsRules) {
            super(itrsProblem, removedArgsRules);
            //this.groundTerms = groundTermsParam;
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
                "Some arguments are removed because they always contain the same ground term.");
            sb.append(eu.linebreak());
            /*sb.append("We removed the following ground terms:");
            sb.append(eu.linebreak());
            sb.append(eu.set(this.groundTerms, 3));
            sb.append(eu.linebreak());*/
            super.export(eu, sb);
            return sb.toString();
        }
    }

    /**
     * Fill in functionApplications, definedSymbols, syms from the itrs.
     * Initialize groundTerms to a map which assigns null to each integer
     * for each function symbol
     * @param i the TRS
     */
    private void init(final Set<GeneralizedRule> rules,
            final IDPPredefinedMap predefinedMap,
            final Collection<TRSFunctionApplication> functionApplications,
            final Map<FunctionSymbol, Map<Integer, TRSTerm>> groundTerms,
            final Collection<FunctionSymbol> syms,
            final Collection<FunctionSymbol> definedSymbols) {
        // Now, find all applications
        final LinkedList<TRSTerm> terms = new LinkedList<TRSTerm>();
        for (final GeneralizedRule r : rules) {
            terms.addAll(r.getTerms());
        }
        while (!terms.isEmpty()) {
            final TRSTerm term = terms.pop();
            if (term.isVariable()) {
                continue;
            }
            final TRSFunctionApplication fa = (TRSFunctionApplication) term;
            terms.addAll(fa.getArguments());
            final FunctionSymbol fs = fa.getRootSymbol();
            if (!predefinedMap.isPredefined(fs) && !fs.equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL)) {
                syms.add(fs);
                functionApplications.add(fa);
            }
        }

        // Find out which symbols are defined
        for (final GeneralizedRule rule : rules) {
            definedSymbols.add(rule.getRootSymbol());
        }

        /*
         * For every function symbol and every argument position mark the
         * corresponding positions to the left.
         */
        for (final FunctionSymbol fs : syms) {
            final int arity = fs.getArity();
            if (arity == 0) {
                continue;
            }
            // do not ever try to modify predefined function symbols
            if (predefinedMap.isPredefined(fs) || fs.equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL)) {
                continue;
            }
            final Map<Integer, TRSTerm> groundColl = new LinkedHashMap<Integer, TRSTerm>();
            for (int j = 0; j < arity; j++) {
                final Integer iInt = Integer.valueOf(j);
                groundColl.put(iInt, null);
            }
            groundTerms.put(fs, groundColl);
        }
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

    public Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                  Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                  Collection<Rule>> processRulePair(
            final Set<GeneralizedRule> pRules,
            final Set<GeneralizedRule> rRules,
            final IDPPredefinedMap predefinedMap) {
        /**
         * Function applications occuring in the TRS
         */
        final Collection<TRSFunctionApplication> functionApplications =
            new LinkedHashSet<TRSFunctionApplication>();

        /**
         * Function symbols occuring in the TRS
         */
        final Collection<FunctionSymbol> syms =
            new LinkedHashSet<FunctionSymbol>();

        /**
         * For each function symbol a map from a position in a function application
         * with that function symbol as root symbol to a term we've already seen
         * in that function application.
         *
         * e.g. if f(1, 2) is in the trs, then f -> (1 -> 1, 2 -> 2) could be in this map
         */
        final Map<FunctionSymbol, Map<Integer, TRSTerm>> groundTerms =
            new LinkedHashMap<FunctionSymbol, Map<Integer, TRSTerm>>();

        /**
         * Function symbols defined in the TRS
         */
        final Collection<FunctionSymbol> definedSymbols =
            new LinkedHashSet<FunctionSymbol>();

        //Call init twice, once for each rule set:
        this.init(pRules, predefinedMap, functionApplications, groundTerms, syms, definedSymbols);
        this.init(rRules, predefinedMap, functionApplications, groundTerms, syms, definedSymbols);

        /*
         * Now, for every function application and position inside check if at
         * that position the same constant term appears that was already seen.
         */
        for (final TRSFunctionApplication fa : functionApplications) {
            final FunctionSymbol rootFS = fa.getRootSymbol();
            final int arity = rootFS.getArity();
            if (arity == 0) {
                continue;
            }
            final Map<Integer, TRSTerm> groundColl = groundTerms.get(rootFS);

            /*
             * Now, for the current function application, check if the term
             * seen here is identical to the term we already know for that
             * position.
             */
            /*
             * If we know, that we cannot filter a position in the term,
             * we add that position to this collection.
             * We do it this way because we need to remove items from
             * groundColl, over which we iterate.
             */
            final Collection<Integer> remove = new LinkedList<Integer>();
            final Map<Integer, TRSTerm> newSeen =
                new LinkedHashMap<Integer, TRSTerm>();
            for (final Map.Entry<Integer, TRSTerm> entry : groundColl.entrySet()) {
                final Integer pos = entry.getKey();
                final TRSTerm termAtPos = fa.getArgument(pos.intValue());
                if (termAtPos instanceof TRSFunctionApplication) {
                    final FunctionSymbol fs =
                        ((TRSFunctionApplication) termAtPos).getRootSymbol();
                    if (definedSymbols.contains(fs)) {
                        remove.add(pos);
                        continue;
                    }
                }
                if (!termAtPos.isGroundTerm()) {
                    // If at some position the term is not a ground term, then this position
                    // cannot be removed
                    remove.add(pos);
                    continue;
                }
                // If at some position there is a defined symbol in the term,
                // then this position cannot be removed
                for (final FunctionSymbol s : termAtPos.getFunctionSymbols()) {
                    if (definedSymbols.contains(s)) {
                        remove.add(pos);
                        continue;
                    }
                }

                // If for some position there is a function symbol for which
                // we have another function application with the same
                // root symbol and a different term at that same position,
                // then the position cannot be removed
                TRSTerm knownTerm = groundColl.get(pos);
                if (knownTerm == null) {
                    knownTerm = newSeen.get(pos);
                }
                if (knownTerm == null) {
                    // first time we see this position
                    newSeen.put(pos, termAtPos);
                } else if (!knownTerm.equals(termAtPos)) {
                    // different ground terms :(
                    remove.add(pos);
                }
            }
            for (final Integer rem : remove) {
                groundColl.remove(rem);
            }
            groundColl.putAll(newSeen);
        }

        // For every function symbol mark the positions that can be deleted
        boolean didSomething = false;
        final CollectionMap<FunctionSymbol, Integer> positionsToBeRemoved =
            new CollectionMap<FunctionSymbol, Integer>();
        for (final FunctionSymbol sym : syms) {
            if (sym.getArity() == 0) {
                continue;
            }

            // what about the ground terms?
            final Map<Integer, TRSTerm> groundColl = groundTerms.get(sym);

            if (!groundColl.isEmpty()) {
                didSomething = true;
                positionsToBeRemoved.add(sym, groundColl.keySet());
            }
        }

        if (!didSomething) {
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
                          Collection<Rule>>(newPPair, newRPair, ArgumentsRemovalProof.getFilterRules(positionsToBeRemoved, newPPair.y));
    }

    /**
     * Start working on the given ITRS.
     * @param itrs some itrs
     * @param aborter an aborter
     * @return the ITRS with useless ground terms removed (together with a proof
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

        final GroundTermsRemoverProof proof =
            new GroundTermsRemoverProof(itrs, positionsToBeRemoved);
        return ResultFactory.proved(newItrs, YNMImplication.EQUIVALENT, proof);
    }

}
