package aprove.verification.idpframework.Algorithms.Matching;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class PositionalMatchUnification<K> {

    private CollectionMap<IFunctionSymbol<?>, MatchingTableEntry> matchingTable;
    private BidirectionalMap<ITerm<?>, Integer> termIds;
    private LinkedHashMap<Integer, IVariable<?>> varIds;
    private LinkedHashMap<Integer, K> numberKeys;
    private LinkedHashSet<Integer> rootTermIds;

    public PositionalMatchUnification(final Map<ITerm<?>, K> terms) {
        this.buildMatchingTable(terms);
    }

    public CollectionMap<IPosition, TermMatchUnif<K>> getMatchesToTerm(final ITerm<?> t) {
        final CollectionMap<IPosition, TermMatchUnif<K>> matches = new CollectionMap<IPosition, TermMatchUnif<K>>();

        this.getTermDescriptions(IPosition.create(), true, t, matches);

        return matches;
    }

    public CollectionMap<IPosition, TermMatchUnif<K>> getUnificationsForTerm(final ITerm<?> t) {
        final CollectionMap<IPosition, TermMatchUnif<K>> matches = new CollectionMap<IPosition, TermMatchUnif<K>>();

        this.getTermDescriptions(IPosition.create(), false, t, matches);

        return matches;
    }

    protected CollectionMap<Integer, ISubstitution> getTermDescriptions(final IPosition currentPosition,
        final boolean requireMatching,
        final ITerm<?> t,
        final CollectionMap<IPosition, TermMatchUnif<K>> matches) {

        final CollectionMap<Integer, ISubstitution> res = new CollectionMap<Integer, ISubstitution>();

        for (final Map.Entry<Integer, IVariable<?>> varId : this.varIds.entrySet()) {
            final IVariable<?> matchingVar = varId.getValue();
            if (matchingVar.getDomain().isSpecialization(t.getDomain())) {
                res.add(varId.getKey(), ISubstitution.create(varId.getValue(), t));
            }
        }

        if (t.isVariable()) {
            if (!requireMatching) {
                final IVariable<?> tVar = (IVariable<?>) t;
                for (final Map.Entry<ITerm<?>, Integer> termId : this.termIds.getEntriesLR()) {
                    final ITerm<?> matchingTerm = termId.getKey();
                    if (t.getDomain().isSpecialization(matchingTerm.getDomain())) {
                        res.add(termId.getValue(), ISubstitution.create(tVar, matchingTerm));
                    }
                }
            }
        } else {
            final IFunctionApplication<?> fa = (IFunctionApplication<?>) t;

            final ArrayList<CollectionMap<Integer, ISubstitution>> argList =
                new ArrayList<CollectionMap<Integer, ISubstitution>>(fa.getArguments().size());

            boolean allArgsValid = true;

            final int aurgumentCount = fa.getArguments().size();
            for (int argIndex = 0; argIndex < aurgumentCount; argIndex++) {
                final ITerm<?> arg = fa.getArgument(argIndex);

                final CollectionMap<Integer, ISubstitution> argTermDescriptions =
                    this.getTermDescriptions(currentPosition.append(argIndex), requireMatching, arg, matches);

                if (argTermDescriptions.isEmpty()) {
                    allArgsValid = false;
                }

                argList.add(argTermDescriptions);
            }

            if (allArgsValid) {
                final Collection<MatchingTableEntry> matchingTableEntry = this.matchingTable.get(fa.getRootSymbol());
                if (matchingTableEntry != null) {
                    matchingTableEntries : for (final MatchingTableEntry entry : matchingTableEntry) {
                        LinkedHashSet<ISubstitution> entrySubstitutions = new LinkedHashSet<ISubstitution>();
                        entrySubstitutions.add(ISubstitution.emptySubstitution());
                        final ImmutableArrayList<Integer> argTermList = entry.getArgTermList();

                        for (int argIndex = argTermList.size() - 1; argIndex >= 0; argIndex--) {
                            final Integer argType = argTermList.get(argIndex);
                            final CollectionMap<Integer, ISubstitution> argTermDescriptions =
                                argList.get(argIndex);
                            final Collection<ISubstitution> possibleArgSubstitutions =
                                argTermDescriptions.get(argType);

                            if (possibleArgSubstitutions != null) {
                                if (requireMatching) {
                                    entrySubstitutions = this.mergeMatchingSubstitutions(entrySubstitutions,
                                        possibleArgSubstitutions,
                                        entry.isLinear());
                                } else {
                                    entrySubstitutions = this.mergeUnificationSubstitutions(entrySubstitutions,
                                        possibleArgSubstitutions);
                                }
                                if (entrySubstitutions.isEmpty()) {
                                    continue matchingTableEntries;
                                }
                            } else {
                                continue matchingTableEntries;
                            }
                        }

                        res.add(entry.getTermId(), entrySubstitutions);
                    }
                }
            }
        }

        for (final Map.Entry<Integer, Collection<ISubstitution>> resEntry : res.entrySet()) {
            if (this.rootTermIds.contains(resEntry.getKey())) {
                final ITerm<?> matchingTerm = this.termIds.getRL(resEntry.getKey());
                assert matchingTerm != null;
                final K key = this.numberKeys.get(resEntry.getKey());

                for (final ISubstitution subst : resEntry.getValue()) {
                    matches.add(currentPosition, new TermMatchUnif<K>(key, matchingTerm, subst));
                }
            }
        }

        return res;
    }

    private LinkedHashSet<ISubstitution> mergeMatchingSubstitutions(
        final LinkedHashSet<ISubstitution> entrySubstitutions,
        final Collection<ISubstitution> possibleArgSubstitutions, final boolean linearMerge) {
        final LinkedHashSet<ISubstitution> res = new LinkedHashSet<ISubstitution>();
        for (final ISubstitution entrySubstitution : entrySubstitutions) {
            substSearch : for (final ISubstitution possibleArgSubstitution : possibleArgSubstitutions) {
                final Map<IVariable<?>, ITerm<?>> subst = new LinkedHashMap<IVariable<?>, ITerm<?>>();
                subst.putAll(entrySubstitution.getMap());
                if (linearMerge) {
                    subst.putAll(possibleArgSubstitution.getMap());
                    res.add(ISubstitution.create(ImmutableCreator.create(subst)));
                } else {
                    for (final Map.Entry<IVariable<?>, ? extends ITerm<?>> substEntry : possibleArgSubstitution.getMap().entrySet()) {
                        final ITerm<?> replaced = subst.put(substEntry.getKey(), substEntry.getValue());
                        if (replaced != null) {
                            if (!replaced.equals(substEntry.getValue())) {
                                continue substSearch;
                            }
                        }
                    }

                    res.add(ISubstitution.create(ImmutableCreator.create(subst)));
                }
            }
        }
        return res;
    }

    private LinkedHashSet<ISubstitution> mergeUnificationSubstitutions(
        final LinkedHashSet<ISubstitution> entrySubstitutions,
        final Collection<ISubstitution> possibleArgSubstitutions) {
        final LinkedHashSet<ISubstitution> res = new LinkedHashSet<ISubstitution>();
        for (final ISubstitution entrySubstitution : entrySubstitutions) {
            substSearch : for (final ISubstitution possibleArgSubstitution : possibleArgSubstitutions) {
                final Map<IVariable<?>, ITerm<?>> subst = new LinkedHashMap<IVariable<?>, ITerm<?>>();
                subst.putAll(entrySubstitution.getMap());

                for (final Map.Entry<IVariable<?>, ? extends ITerm<?>> substEntry : possibleArgSubstitution.getMap().entrySet()) {
                    // chech occur failure
                    if (substEntry.getValue().hasSubterm(substEntry.getKey())) {
                        continue substSearch;
                    }

                    final ITerm<?> replaced = subst.put(substEntry.getKey(), substEntry.getValue());
                    if (replaced != null) {
                        if (!replaced.unifies(substEntry.getValue())) {
                            continue substSearch;
                        }
                    }
                }
            }
        }
        return res;
    }

    private void buildMatchingTable(final Map<ITerm<?>, K> terms) {
        this.matchingTable = new CollectionMap<IFunctionSymbol<?>, PositionalMatchUnification.MatchingTableEntry>();
        this.termIds = new BidirectionalMap<ITerm<?>, Integer>();
        this.varIds = new LinkedHashMap<Integer, IVariable<?>>();
        this.numberKeys = new LinkedHashMap<Integer, K>();
        this.rootTermIds = new LinkedHashSet<Integer>();

        final FreshIntegerGenerator freshTermNumbers = new FreshIntegerGenerator(true);
        final FreshIntegerGenerator freshVarNumbers = new FreshIntegerGenerator(false);

        for (final Map.Entry<ITerm<?>, K> termKey : terms.entrySet()) {
            final int termId = this.buildMatchingTable(termKey.getKey(),
                termKey.getValue(),
                this.matchingTable,
                this.termIds,
                this.varIds,
                this.numberKeys,
                freshTermNumbers,
                freshVarNumbers);

            this.rootTermIds.add(termId);
        }
    }

    private int buildMatchingTable(final ITerm<?> term,
        final K key,
        final CollectionMap<IFunctionSymbol<?>, MatchingTableEntry> matchingTable,
        final BidirectionalMap<ITerm<?>, Integer> termNumbers,
        final Map<Integer, IVariable<?>> varNumbers,
        final Map<Integer, K> numberKeys,
        final FreshIntegerGenerator freshTermNumbers,
        final FreshIntegerGenerator freshVarNumbers) {
        if (!termNumbers.containsKeyLR(term)) {
            if (term.isVariable()) {
                final Integer termId = freshVarNumbers.getNextValue();
                termNumbers.putLR(term, termId);
                varNumbers.put(termId, (IVariable<?>) term);
                return termId;
            } else {
                final IFunctionApplication<?> fa = (IFunctionApplication<?>) term;
                final ArrayList<Integer> argList = new ArrayList<Integer>(fa.getArguments().size());

                for (final ITerm<?> arg : fa.getArguments()) {
                    final int argTermId = this.buildMatchingTable(arg,
                        key,
                        matchingTable,
                        termNumbers,
                        varNumbers,
                        numberKeys,
                        freshTermNumbers,
                        freshVarNumbers);

                    argList.add(argTermId);
                }

                final int termId = freshTermNumbers.getNextValue();
                termNumbers.putLR(term, termId);

                final MatchingTableEntry matchingTableEntry =
                    new MatchingTableEntry(termId,
                        ImmutableCreator.create(argList),
                        fa.isLinear());

                matchingTable.add(fa.getRootSymbol(), matchingTableEntry);

                return termId;
            }
        } else {
            return termNumbers.getLR(term);
        }
    }


    protected static class MatchingTableEntry {

        private final int termId;
        private final ImmutableArrayList<Integer> argTermList;
        private final boolean isLinear;

        public MatchingTableEntry(final int termId, final ImmutableArrayList<Integer> argTermList, final boolean isLinear) {
            this.termId = termId;
            this.argTermList = argTermList;
            this.isLinear = isLinear;
        }

        public int getTermId() {
            return this.termId;
        }

        public ImmutableArrayList<Integer> getArgTermList() {
            return this.argTermList;
        }

        public boolean isLinear() {
            return this.isLinear;
        }
    }

    protected static class FreshIntegerGenerator {

        private final boolean positive;
        private int nextValue;


        public FreshIntegerGenerator (final boolean positive) {
            this.positive = positive;

            if (positive) {
                this.nextValue = 0;
            } else {
                this.nextValue = -1;
            }
        }

        public int getNextValue() {
            if (this.positive) {
                return this.nextValue ++;
            } else {
                return this.nextValue --;
            }
        }
    }
}