package aprove.verification.idpframework.Algorithms.Confluence;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Critical Pairs can be questioned about: 1) non-overlappingness 2) overlay
 * systems 3) local confluence (w.r.t. some join limit)
 * @author Martin Pluecker, copied from thiemann
 */
public class CriticalPairs {

    // the critical pairs, null if all info has been gathered
    private volatile AbortableIterator<ImmutableTriple<ITerm<?>, ITerm<?>, Boolean>> critPairIterator;

    //  the map to join the critical pairs. maybe null in the beginning, then no joinability property may be asked.
    //  after joinability questions have been asked, ruleMap is set to null.
    private Map<IFunctionSymbol<?>, ? extends Set<? extends IRule>> ruleMap;

    private Boolean gotRootCritpairs;
    private Boolean gotNonRootCritpairs; // are there any critical pairs from non-root overlaps
    private Boolean gotCritpair; // are there any critical pairs
    private Boolean gotNonTrivialCritpair; // are there any non-trivial critical pairs

    //  the set of possibly non-joinable critical pairs.
    //  the integer is the limit on how many steps we have performed to join these terms. null if localConfluence is determined.
    private Collection<Triple<ITerm<?>, ITerm<?>, Integer>> nonJoinableCritPairs;

    private YNM localConfluence; // null, if ruleMap is empty, the logical value otherwise
    private int limit; // we have tested to join crit pairs in at most limit steps

    /**
     * creates a new critical pair object. R and ruleMap have to correspond to
     * one another.
     * @param R
     * @param ruleMap
     */
    public CriticalPairs(final Set<? extends IRule> rls,
            final Map<IFunctionSymbol<?>, ? extends Set<? extends IRule>> ruleMap) {
        if (Globals.useAssertions) {
            assert (ruleMap != null && rls != null);
        }
        this.critPairIterator = ConfluenceFactory.getCriticalPairs(rls);
        this.ruleMap = ruleMap;
        this.gotNonRootCritpairs = null;
        this.gotCritpair = null;
        this.gotRootCritpairs = null;
        this.gotNonTrivialCritpair = null;
        this.nonJoinableCritPairs =
            ruleMap == null ? null
                : new LinkedList<Triple<ITerm<?>, ITerm<?>, Integer>>();
        this.localConfluence = ruleMap == null ? null : YNM.MAYBE;
        this.limit = 0;
    }

    /**
     * checks whether we have a non-overlapping set of rules
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized boolean isNonOverlapping(final Abortion aborter)
            throws AbortionException {
        if (this.gotCritpair == null) {
            this.getNextCritPair(aborter, YNM.YES);
        }
        return !this.gotCritpair;
    }

    /**
     * checks whether we have a an overlay TRS, ie. where the only critical
     * pairs are on root level
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized boolean isOverlay(final Abortion aborter)
            throws AbortionException {
        if (this.gotNonRootCritpairs == null) {
            this.getNextCritPair(aborter, YNM.MAYBE);
        }
        return !this.gotNonRootCritpairs;
    }

    /**
     * checks whether we have a non-overlaying TRS, ie. where there are no
     * critical pairs on root level
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized boolean isNonOverlaying(final Abortion aborter)
            throws AbortionException {
        if (this.gotRootCritpairs == null) {
            this.getNextCritPair(aborter, YNM.YES);
        }
        return !this.gotRootCritpairs;
    }

    /**
     * checks whether the TRS is locally confluent. The nr of steps to join
     * critical pairs is at least the given limit (but sometimes decompositions
     * and caching say join although the number of steps one needs is higher
     * than limit). If this method is called one must have provided a qtrs or a
     * rule map in the constructor.
     * @param limit
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized YNM isLocallyConfluent(final int limit,
        final Abortion aborter) throws AbortionException {
        if (this.critPairIterator != null) {
            this.getNextCritPair(aborter, YNM.NO);
        }
        if (this.limit >= limit || this.localConfluence.isBool()) {
            return this.localConfluence;
        }
        this.checkJoin(limit, aborter);
        return this.localConfluence;
    }

    public synchronized boolean onlyTrivialCriticalPairs(final Abortion aborter)
            throws AbortionException {
        if (this.gotNonTrivialCritpair == null) {
            this.getNextCritPair(aborter, YNM.NO);
        }
        return !this.gotNonTrivialCritpair;
    }

    private final static Integer ZERO = 0;

    /**
     * computes one next critical pair or all critical pairs
     * @param aborter
     * @param one YES: only generate next crit pair. NO: generate all crit
     * pairs, MAYBE: generate all crit pairs until we can decide whether TRS is
     * overlay
     * @throws AbortionException
     */
    private final void getNextCritPair(final Abortion aborter, final YNM one)
            throws AbortionException {
        if (this.critPairIterator != null) {
            synchronized (this) {
                if (this.critPairIterator != null) {
                    final ArrayStack<Triple<ITerm<?>, ITerm<?>, Integer>> todoList =
                        new ArrayStack<Triple<ITerm<?>, ITerm<?>, Integer>>();
                    boolean notDone = true;
                    while (notDone) {
                        if (one == YNM.YES) {
                            notDone = false;
                        }
                        if (this.critPairIterator.hasNext(aborter)) {
                            final ImmutableTriple<ITerm<?>, ITerm<?>, Boolean> critPair =
                                this.critPairIterator.next(aborter);
                            if (this.gotCritpair == null) {
                                // found first critical pair
                                this.gotCritpair = Boolean.TRUE;
                                if (critPair.z.booleanValue()) {
                                    this.gotRootCritpairs = Boolean.TRUE;
                                } else {
                                    this.gotRootCritpairs = Boolean.FALSE;
                                    this.gotNonRootCritpairs = Boolean.TRUE;
                                    if (one == YNM.MAYBE) {
                                        notDone = false;
                                    }
                                }
                            } else {
                                // found later critical pair
                                if (this.gotNonRootCritpairs == null
                                    && !critPair.z) {
                                    // detected first nonRoot critpair
                                    this.gotNonRootCritpairs = Boolean.TRUE;
                                    if (one == YNM.MAYBE) {
                                        notDone = false;
                                    }
                                }
                            }

                            // we have found a critical pair.
                            // now drop outermost constructors of s and t and check for equality.
                            final ITerm<?> s = critPair.x;
                            final ITerm<?> t = critPair.y;
                            if (this.gotNonTrivialCritpair == null
                                && !s.equals(t)) {
                                this.gotNonTrivialCritpair = true;
                            }
                            todoList.clear();
                            todoList.push(new Triple<ITerm<?>, ITerm<?>, Integer>(s,
                                t, CriticalPairs.ZERO));
                            while (!todoList.isEmpty()) {
                                final Triple<ITerm<?>, ITerm<?>, Integer> todo =
                                    todoList.pop();
                                final ITerm<?> si = todo.x;
                                final ITerm<?> ti = todo.y;
                                if (!si.equals(ti)) {

                                    if (si instanceof IFunctionApplication<?>
                                        && ti instanceof IFunctionApplication<?>) {
                                        final IFunctionApplication<?> fsi =
                                            (IFunctionApplication<?>) si;
                                        final IFunctionSymbol<?> f =
                                            fsi.getRootSymbol();
                                        if (this.ruleMap.containsKey(f)) {
                                            this.nonJoinableCritPairs.add(todo);
                                            continue;
                                        } else {
                                            final IFunctionApplication<?> gti =
                                                (IFunctionApplication<?>) ti;
                                            final IFunctionSymbol<?> g =
                                                gti.getRootSymbol();
                                            if (this.ruleMap.containsKey(g)) {
                                                this.nonJoinableCritPairs.add(todo);
                                                continue;
                                            } else {
                                                if (f.equals(g)) {
                                                    // we have equal outermost constructors -> arguments must be joinable
                                                    final Iterator<? extends ITerm<?>> siArgs =
                                                        fsi.getArguments().iterator();
                                                    for (final ITerm<?> tiArg : gti.getArguments()) {
                                                        final ITerm<?> siArg =
                                                            siArgs.next();
                                                        todoList.push(new Triple<ITerm<?>, ITerm<?>, Integer>(
                                                            siArg, tiArg, CriticalPairs.ZERO));
                                                    }
                                                } else {
                                                    // we have different outermost constructors -> never joinable
                                                    this.localConfluence =
                                                        YNM.NO;
                                                    this.ruleMap = null;
                                                    this.nonJoinableCritPairs =
                                                        null;
                                                    // we possible have to determine whether there are non root critical pairs
                                                    while (this.gotNonRootCritpairs == null) {
                                                        if (this.critPairIterator.hasNext(aborter)) {
                                                            if (this.critPairIterator.next(aborter).z) {
                                                                // another root overlap
                                                            } else {
                                                                // non root overlap
                                                                this.gotNonRootCritpairs =
                                                                    Boolean.TRUE;
                                                            }
                                                        } else {
                                                            this.gotNonRootCritpairs =
                                                                Boolean.FALSE;
                                                        }
                                                    }
                                                    this.critPairIterator =
                                                        null;
                                                    return;
                                                }
                                            }
                                        }
                                    } else {
                                        this.nonJoinableCritPairs.add(todo);
                                        continue;
                                    }

                                }

                            }
                        } else {
                            // there are no further critical pairs.
                            notDone = false;
                            this.critPairIterator = null;
                            if (this.gotNonTrivialCritpair == null) {
                                this.gotNonTrivialCritpair = false;
                            }
                            if (this.gotCritpair == null) {
                                // there are no critical pairs
                                this.gotCritpair = Boolean.FALSE;
                                this.gotRootCritpairs = Boolean.FALSE;
                                this.gotNonRootCritpairs = Boolean.FALSE;
                                this.ruleMap = null;
                                this.nonJoinableCritPairs = null;
                                this.localConfluence = YNM.YES;
                            } else {
                                // we have seen all critical pairs, at least one
                                if (this.gotNonRootCritpairs == null) {
                                    this.gotNonRootCritpairs = Boolean.FALSE;
                                }
                                if (this.nonJoinableCritPairs.isEmpty()) {
                                    this.localConfluence = YNM.YES;
                                    this.nonJoinableCritPairs = null;
                                } else {
                                    this.localConfluence = YNM.MAYBE;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private final synchronized void checkJoin(final int limit,
        final Abortion aborter) throws AbortionException {
        // another test inside the synchronized because of racing conditions:
        // two threads might want to run checkJoin, where the first changes
        // this.localConfluence to non-maybe (and nulls nonJoinCritPairs).
        if (limit > this.limit && this.localConfluence == YNM.MAYBE
            && this.nonJoinableCritPairs != null) {
            final Map<IFunctionSymbol<?>, ? extends Set<? extends UnconditionalIRule>> filteredRuleMap =
                IRuleFactory.retainUnconditional(this.ruleMap);
            final Iterator<Triple<ITerm<?>, ITerm<?>, Integer>> critPairIter =
                this.nonJoinableCritPairs.iterator();
            while (critPairIter.hasNext()) {
                aborter.checkAbortion();
                final Triple<ITerm<?>, ITerm<?>, Integer> critPair =
                    critPairIter.next();
                final YNM result =
                    CriticalPairs.critPairIsJoinable(critPair.x, critPair.y, critPair.z,
                        limit, filteredRuleMap, aborter);
                if (result == YNM.YES) {
                    critPairIter.remove();
                } else if (result == YNM.NO) {
                    this.localConfluence = YNM.NO;
                    this.ruleMap = null;
                    this.nonJoinableCritPairs = null;
                    return;
                } else {
                    this.limit = limit;
                    // one might do a return here,
                    // but we also search the other pairs for possible no's
                }
            }
            if (this.nonJoinableCritPairs.isEmpty()) {
                this.localConfluence = YNM.YES;
                this.nonJoinableCritPairs = null;
                this.ruleMap = null;
            }
        }
    }

    private static final int countSteps = 1 << 6;

    /**
     * Check if a given critical pair is joinable in <code>limit</code>
     * rewriting steps, where it has been checked that it is not joinable in
     * start steps.
     * @param start a natural number
     * @param limit a natural number
     * @throws AbortionException
     */
    static final <T extends IRule> YNM critPairIsJoinable(final ITerm<?> cpLeft,
        final ITerm<?> cpRight,
        final int start,
        final int limit,
        final Map<IFunctionSymbol<?>, ? extends Set<? extends UnconditionalIRule>> Rls,
        final Abortion aborter) throws AbortionException {
        int count = 0;
        // is the critical pair directly joinable?
        if (start >= limit) {
            return YNM.MAYBE;
        }

        Set<ITerm<?>> leftNewTerms = new LinkedHashSet<ITerm<?>>();
        Set<ITerm<?>> leftVeryNewTerms = new LinkedHashSet<ITerm<?>>();
        final Set<ITerm<?>> leftAllTerms = new LinkedHashSet<ITerm<?>>();
        Set<ITerm<?>> rightVeryNewTerms = new LinkedHashSet<ITerm<?>>();
        leftNewTerms.add(cpLeft);
        leftAllTerms.add(cpLeft);
        Set<ITerm<?>> rightNewTerms = new LinkedHashSet<ITerm<?>>();
        final Set<ITerm<?>> rightAllTerms = new LinkedHashSet<ITerm<?>>();
        rightNewTerms.add(cpRight);
        rightAllTerms.add(cpRight);

        Set<ITerm<?>> exchange;
        final FreshNameGenerator freshNames =
            new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        freshNames.lockNames(CollectionUtils.getNames(cpLeft.getVariables()));
        freshNames.lockNames(CollectionUtils.getNames(cpRight.getVariables()));

        for (int i = 0; i < limit; i++) {
            // rewrite only those terms which have not been rewritten yet
            for (final ITerm<?> leftNewTerm : leftNewTerms) {
                final Set<ITerm<?>> leftRewriteTerms =
                    leftNewTerm.rewrite(Rls, freshNames);
                for (final ITerm<?> leftRewriteTerm : leftRewriteTerms) {
                    count++;
                    if ((count & CriticalPairs.countSteps) != 0) {
                        aborter.checkAbortion();
                    }
                    if (leftAllTerms.add(leftRewriteTerm)) {
                        if (i >= start
                            && rightAllTerms.contains(leftRewriteTerm)) {
                            return YNM.YES;
                        }
                        leftVeryNewTerms.add(leftRewriteTerm);
                    }
                }
            }
            // for next iteration
            exchange = leftNewTerms;
            leftNewTerms = leftVeryNewTerms;
            leftVeryNewTerms = exchange;
            leftVeryNewTerms.clear();

            // rewrite only those terms which have not been rewrited yet
            for (final ITerm<?> rightNewTerm : rightNewTerms) {
                final Set<ITerm<?>> rightRewriteTerms =
                    rightNewTerm.rewrite(Rls, freshNames);
                for (final ITerm<?> rightRewriteTerm : rightRewriteTerms) {
                    if ((count & CriticalPairs.countSteps) != 0) {
                        aborter.checkAbortion();
                    }
                    if (rightAllTerms.add(rightRewriteTerm)) {
                        if (i >= start
                            && leftAllTerms.contains(rightRewriteTerm)) {
                            return YNM.YES;
                        }
                        rightVeryNewTerms.add(rightRewriteTerm);
                    }
                }
            }
            //for next iteration
            exchange = rightNewTerms;
            rightNewTerms = rightVeryNewTerms;
            rightVeryNewTerms = exchange;
            rightVeryNewTerms.clear();

            // no more rewrite steps possible
            if (leftNewTerms.isEmpty() && rightNewTerms.isEmpty()) {
                return YNM.NO; // the terms are not joinable independent of limit.
            }

        }

        // the terms are not joinable in limit steps
        return YNM.MAYBE;
    }

}
