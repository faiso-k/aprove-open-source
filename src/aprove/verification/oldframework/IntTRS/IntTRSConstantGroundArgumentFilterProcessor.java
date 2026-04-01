package aprove.verification.oldframework.IntTRS;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

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
 * @author cotto, Christian von Essen, Marc Brockschmidt
 */
public class IntTRSConstantGroundArgumentFilterProcessor extends IntTRSArgumentFilter {
    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSLike : "Wrong obligation type!";
        final IRSLike intTRS = (IRSLike) obl;

        final Pair<Pair<Set<IGeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>, CollectionMap<FunctionSymbol, Integer>> r =
            IntTRSConstantGroundArgumentFilterProcessor.processRules(intTRS.getRules());

        if (r != null) {
            final TRSFunctionApplication newStartTerm;
            if (intTRS.getStartTerm() != null) {
                newStartTerm =
                    (TRSFunctionApplication) HelperClass.remove(
                        intTRS.getStartTerm(),
                        r.y,
                        r.x.y,
                        r.y.keySet(),
                        IDPPredefinedMap.DEFAULT_MAP);
            } else {
                newStartTerm = null;
            }

            return ResultFactory.proved(
                intTRS.create(r.x.x, newStartTerm),
                YNMImplication.EQUIVALENT,
                new IntTRSConstantGroundArgumentFilterProof(ArgumentsRemovalProof.getFilterRules(r.y, r.x.y)));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    /**
     * Fill in functionApplications, definedSymbols, syms from the itrs.
     * Initialize groundTerms to a map which assigns null to each integer
     * for each function symbol
     */
    private static void init(
        final Set<IGeneralizedRule> rules,
        final IDPPredefinedMap predefinedMap,
        final Collection<TRSFunctionApplication> functionApplications,
        final Map<FunctionSymbol, Map<Integer, TRSTerm>> groundTerms,
        final Collection<FunctionSymbol> syms,
        final Collection<FunctionSymbol> definedSymbols)
    {
        // Now, find all applications
        final LinkedList<TRSTerm> terms = new LinkedList<>();
        for (final IGeneralizedRule r : rules) {
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
        for (final IGeneralizedRule rule : rules) {
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
            final Map<Integer, TRSTerm> groundColl = new LinkedHashMap<>();
            for (int j = 0; j < arity; j++) {
                final Integer iInt = Integer.valueOf(j);
                groundColl.put(iInt, null);
            }
            groundTerms.put(fs, groundColl);
        }
    }

    /**
     * @param rules some set of rules
     * @return a pair of filtered rules and a mapping detailing which positions are to be filtered
     */
    public static
        Pair<Pair<Set<IGeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>, CollectionMap<FunctionSymbol, Integer>>
        processRules(final Set<IGeneralizedRule> rules)
    {
        return IntTRSConstantGroundArgumentFilterProcessor.processRules(rules, java.util.Collections.<FunctionSymbol>emptySet());
    }

    /**
     * @param rules some set of rules
     * @return a pair of filtered rules and a mapping detailing which positions are to be filtered
     */
    public static
        Pair<Pair<Set<IGeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>, CollectionMap<FunctionSymbol, Integer>>
        processRules(final Set<IGeneralizedRule> rules, final Set<FunctionSymbol> protectedSymbols)
    {
        final IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        /**
         * Function applications occuring in the TRS
         */
        final Collection<TRSFunctionApplication> functionApplications = new LinkedHashSet<>();

        /**
         * Function symbols occuring in the TRS
         */
        final Collection<FunctionSymbol> syms = new LinkedHashSet<>();

        /**
         * For each function symbol a map from a position in a function application
         * with that function symbol as root symbol to a term we've already seen
         * in that function application.
         *
         * e.g. if f(1, 2) is in the trs, then f -> (1 -> 1, 2 -> 2) could be in this map
         */
        final Map<FunctionSymbol, Map<Integer, TRSTerm>> groundTerms = new LinkedHashMap<>();

        /**
         * Function symbols defined in the TRS
         */
        final Collection<FunctionSymbol> definedSymbols = new LinkedHashSet<>();

        //Call init twice, once for each rule set:
        IntTRSConstantGroundArgumentFilterProcessor.init(rules, predefinedMap, functionApplications, groundTerms, syms, definedSymbols);

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
            final Collection<Integer> remove = new LinkedList<>();
            final Map<Integer, TRSTerm> newSeen = new LinkedHashMap<>();
            for (final Map.Entry<Integer, TRSTerm> entry : groundColl.entrySet()) {
                final Integer pos = entry.getKey();
                final TRSTerm termAtPos = fa.getArgument(pos.intValue());
                if (termAtPos instanceof TRSFunctionApplication) {
                    final FunctionSymbol fs = ((TRSFunctionApplication) termAtPos).getRootSymbol();
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
        final CollectionMap<FunctionSymbol, Integer> positionsToBeRemoved = new CollectionMap<>();
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

        //Do not filter in certain symbols:
        for (final FunctionSymbol protectedSym : protectedSymbols) {
            positionsToBeRemoved.remove(protectedSym);
        }

        if (!didSomething) {
            // No argument can be removed
            return null;
        }

        Map<IGeneralizedRule, IGeneralizedRule> oldNewMap = new HashMap<>();
        // Construct the result
        final Pair<Set<IGeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newRulePair =
            IntTRSArgumentFilter.getResultingRules(rules, positionsToBeRemoved, new LinkedHashSet<FunctionSymbol>(), oldNewMap);

        return new Pair<>(newRulePair, positionsToBeRemoved);
    }

    /**
     * The proof for this processor giving information about the removed positions.
     * @author Marc Brockschmidt
     */
    private class IntTRSConstantGroundArgumentFilterProof extends DefaultProof {
        /**
         * The arguments that are removed.
         */
        private final Collection<Rule> rem;
        final Map<IGeneralizedRule, IGeneralizedRule> oldNewMap;

        /**
         * Create a new proof.
         * @param removedArgs maps function symbols to the list of removed argument positions
         */
        public IntTRSConstantGroundArgumentFilterProof(final Collection<Rule> removedArgs) {
            this.rem = removedArgs;
            this.oldNewMap = null;
        }

        /**
         * @return the proof as a nice string representation.
         * @param o an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Some arguments are removed because they always contain the same ground term.");
            sb.append("We removed arguments according to the following replacements:");
            sb.append(o.linebreak());
            sb.append(o.set(this.rem, Export_Util.RULES));
            return sb.toString();
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return childrenProofs[0];
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            // TODO
            return false && modus.isPositive();
        }        
        
        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData xmlPreMetaData) {
            return xmlPreMetaData.adjustOldNew(this.oldNewMap);
        }

    }
}
