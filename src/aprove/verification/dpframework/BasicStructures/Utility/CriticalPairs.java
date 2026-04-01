package aprove.verification.dpframework.BasicStructures.Utility;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Critical Pairs can be questioned about:
 * 1) non-overlappingness
 * 2) overlay systems
 * 3) local confluence (w.r.t. some join limit)
 *
 * @author thiemann
 *
 */
public class CriticalPairs {

    // the critical pairs, null if all info has been gathered
    private volatile AbortableIterator<ImmutableTriple<TRSTerm, TRSTerm, Boolean>> critPairIterator;

    //  the map to join the critical pairs. maybe null in the beginning, then no joinability property may be asked.
    //  after joinability questions have been asked, ruleMap is set to null.
    private Map<FunctionSymbol, ? extends Set<? extends GeneralizedRule>> ruleMap;

    private Boolean gotNonTrivialRootCritpair; // are there non-trivial critical pairs from root overlaps
    private Boolean gotNonRootCritpairs; // are there any critical pairs from non-root overlaps
    private Boolean gotCritpair; // are there any critical pairs
    private Boolean gotNonTrivialCritpair; // are there any non-trivial critical pairs

    //  the set of possibly non-joinable critical pairs.
    //  the integer is the limit on how many steps we have performed to join these terms. null if localConfluence is determined.
    private Collection<Triple<TRSTerm, TRSTerm, Integer>> nonJoinableCritPairs;


    private YNM localConfluence; // null, if ruleMap is empty, the logical value otherwise
    private int limit; // we have tested to join crit pairs in at most limit steps

    /**
     * creates a critical pair object from the set of rules R in the given qtrs.
     * (Q is disregarded!)
     */
    public CriticalPairs(final QTRSProblem qtrs) {
        this(qtrs.getR(), qtrs.getRuleMap());
    }

    /**
     * creates a new critical pair object. R and ruleMap have to correspond to one another.
     * @param R
     * @param ruleMap
     */
    public CriticalPairs(final Set<? extends GeneralizedRule> rls, final Map<FunctionSymbol, ? extends Set<? extends GeneralizedRule>> ruleMap) {
        if (Globals.useAssertions) {
            assert(ruleMap != null && rls != null);
        }
        this.critPairIterator = GeneralizedRule.getCriticalPairs(rls);
        this.ruleMap = ruleMap;
        this.gotNonRootCritpairs = null;
        this.gotCritpair = null;
        this.gotNonTrivialRootCritpair = null;
        this.gotNonTrivialCritpair = null;
        this.nonJoinableCritPairs = ruleMap == null ? null : new LinkedList<Triple<TRSTerm, TRSTerm, Integer>>();
        this.localConfluence = ruleMap == null ? null : YNM.MAYBE;
        this.limit = 0;
    }

    /**
     * checks whether we have a non-overlapping set of rules
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized boolean isNonOverlapping(final Abortion aborter) throws AbortionException {
        if (this.gotCritpair == null) {
            this.getNextCritPair(aborter, true);
        }
        return !this.gotCritpair;
    }

    /**
     * checks whether we have a an overlay TRS, ie. where the only
     * critical pairs are on root level
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized boolean isOverlay(final Abortion aborter) throws AbortionException {
        if (this.gotNonRootCritpairs == null) {
            this.getNextCritPair(aborter, true);
        }
        return !this.gotNonRootCritpairs;
    }

    /**
     * checks whether we have innermost confluence, where as criterion
     * we check whether all root-overlaps are trivial
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized boolean isInnermostConfluent(final Abortion aborter) throws AbortionException {
        while (this.gotNonTrivialRootCritpair == null) {
            this.getNextCritPair(aborter, true);
        }
        return !this.gotNonTrivialRootCritpair;
    }

    /**
     * checks whether the TRS is locally confluent. The nr of steps to join critical pairs is at
     * least the given limit (but sometimes decompositions and caching say join although the number
     * of steps one needs is higher than limit). If this method is called one must have provided
     * a qtrs or a rule map in the constructor.
     * @param limit
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized YNM isLocallyConfluent(final int limit, final Abortion aborter) throws AbortionException {
        if (this.critPairIterator != null) {
            this.getNextCritPair(aborter, false);
        }
        if (this.limit >= limit || this.localConfluence.isBool()) {
            return this.localConfluence;
        }
        this.checkJoin(limit, aborter);
        return this.localConfluence;
    }

    public synchronized boolean onlyTrivialCriticalPairs(final Abortion aborter) throws AbortionException {
        while (this.gotNonTrivialCritpair == null) {
            this.getNextCritPair(aborter, true);
        }
        return !this.gotNonTrivialCritpair;
    }

    /**
     * computes one next critical pair or all critical pairs
     * @param aborter
     * @param one: only generate one critical pair (true), or generate all critical pairs (false)
     * @throws AbortionException
     */
    private final void getNextCritPair(final Abortion aborter, final boolean one) throws AbortionException {
        if (this.critPairIterator != null) {
            synchronized(this) {
                if (this.critPairIterator != null) {
                    final ArrayStack<Triple<TRSTerm, TRSTerm, Integer>> todoList = new ArrayStack<>();
                    boolean notDone = true;
                    while (notDone) {
                        if (one) {
                            notDone = false;
                        }
                        if (this.critPairIterator.hasNext(aborter)) {
                            ImmutableTriple<TRSTerm, TRSTerm, Boolean> critPair = this.critPairIterator.next(aborter);
                            final TRSTerm s = critPair.x;
                            final TRSTerm t = critPair.y;
                            if (this.gotCritpair == null) {
                                // found first critical pair
                                this.gotCritpair = true;
                                if (critPair.z) {
                                    if (!s.equals(t)) {
                                        this.gotNonTrivialRootCritpair = true;
                                    }
                                    this.gotNonRootCritpairs = false;
                                } else {
                                    this.gotNonRootCritpairs = true;
                                }
                            } else {
                                // found later critical pair
                                if (this.gotNonTrivialRootCritpair == null && critPair.z && !s.equals(t)) {
                                    // detected first critical root critpair
                                    this.gotNonTrivialRootCritpair = true;
                                }
                            }

                            // we have found a critical pair.
                            // now drop outermost constructors of s and t and check for equality.
                            if (this.gotNonTrivialCritpair == null && !s.equals(t)) {
                                this.gotNonTrivialCritpair = true;
                            }
                            todoList.clear();
                            todoList.push(new Triple<>(s, t, 0));
                            while (!todoList.isEmpty()) {
                                final Triple<TRSTerm, TRSTerm, Integer> todo = todoList.pop();
                                final TRSTerm si = todo.x;
                                final TRSTerm ti = todo.y;
                                if (!si.equals(ti)) {

                                    if (si instanceof TRSFunctionApplication && ti instanceof TRSFunctionApplication) {
                                        final TRSFunctionApplication fsi = (TRSFunctionApplication) si;
                                        final FunctionSymbol f = fsi.getRootSymbol();
                                        if (this.ruleMap.containsKey(f)) {
                                            this.nonJoinableCritPairs.add(todo);
                                            continue;
                                        } else {
                                            final TRSFunctionApplication gti = (TRSFunctionApplication) ti;
                                            final FunctionSymbol g = gti.getRootSymbol();
                                            if (this.ruleMap.containsKey(g)) {
                                                this.nonJoinableCritPairs.add(todo);
                                                continue;
                                            } else {
                                                if (f.equals(g)) {
                                                    // we have equal outermost constructors -> arguments must be joinable
                                                    final Iterator<? extends TRSTerm> siArgs = fsi.getArguments().iterator();
                                                    for (final TRSTerm tiArg : gti.getArguments()) {
                                                        final TRSTerm siArg = siArgs.next();
                                                        todoList.push(new Triple<TRSTerm, TRSTerm, Integer>(siArg, tiArg, 0));
                                                    }
                                                } else {
                                                    // we have different outermost constructors -> never joinable
                                                    this.localConfluence = YNM.NO;
                                                    this.ruleMap = null;
                                                    this.nonJoinableCritPairs = null;
                                                    // we possible have to determine whether there are remaining root critical pairs
                                                    while (this.gotNonTrivialRootCritpair == null) {
                                                        if (this.critPairIterator.hasNext(aborter)) {
                                                            critPair = this.critPairIterator.next(aborter);
                                                            if (critPair.z && !critPair.x.equals(critPair.y)) {
                                                                // non trivial root overlap
                                                                this.gotNonTrivialRootCritpair = true;
                                                            }
                                                        } else {
                                                            this.gotNonTrivialRootCritpair = false;
                                                        }
                                                    }
                                                    this.critPairIterator = null;
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
                                this.gotCritpair = false;
                                this.gotNonTrivialRootCritpair = false;
                                this.gotNonRootCritpairs = false;
                                this.ruleMap = null;
                                this.nonJoinableCritPairs = null;
                                this.localConfluence = YNM.YES;
                            } else {
                                // we have seen all critical pairs, at least one
                                if (this.gotNonTrivialRootCritpair == null) {
                                    this.gotNonTrivialRootCritpair = false;
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

    private final synchronized void checkJoin(final int limit, final Abortion aborter) throws AbortionException {
        // another test inside the synchronized because of racing conditions:
        // two threads might want to run checkJoin, where the first changes
        // this.localConfluence to non-maybe (and nulls nonJoinCritPairs).
        if (limit > this.limit && this.localConfluence == YNM.MAYBE && this.nonJoinableCritPairs != null) {
            final Iterator<Triple<TRSTerm, TRSTerm, Integer>> critPairIter = this.nonJoinableCritPairs.iterator();
            while (critPairIter.hasNext()) {
                aborter.checkAbortion();
                final Triple<TRSTerm, TRSTerm, Integer> critPair = critPairIter.next();
                final YNM result = CriticalPairs.critPairIsJoinable(critPair.x, critPair.y, critPair.z, limit, this.ruleMap, aborter);
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
     * Check if a given critical pair is joinable in <code>limit</code> rewriting steps, where it has been checked that
     * it is not joinable in start steps.
     * @param start a natural number
     * @param limit a natural number
     * @throws AbortionException
     */
    static final <T extends GeneralizedRule> YNM critPairIsJoinable(final TRSTerm cpLeft, final TRSTerm cpRight, final int start, final int limit, final Map<FunctionSymbol, ? extends Set<? extends T>> Rls, final Abortion aborter) throws AbortionException {
        int count = 0;
        // is the critical pair directly joinable?
        if (start >= limit) {
            return YNM.MAYBE;
        }

        Set<TRSTerm> leftNewTerms = new LinkedHashSet<TRSTerm>();
        Set<TRSTerm> leftVeryNewTerms = new LinkedHashSet<TRSTerm>();
        final Set<TRSTerm> leftAllTerms = new LinkedHashSet<TRSTerm>();
        Set<TRSTerm> rightVeryNewTerms = new LinkedHashSet<TRSTerm>();
        leftNewTerms.add(cpLeft);
        leftAllTerms.add(cpLeft);
        Set<TRSTerm> rightNewTerms = new LinkedHashSet<TRSTerm>();
        final Set<TRSTerm> rightAllTerms = new LinkedHashSet<TRSTerm>();
        rightNewTerms.add(cpRight);
        rightAllTerms.add(cpRight);

        Set<TRSTerm> exchange;
        final FreshNameGenerator freshNames = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        freshNames.lockNames(CollectionUtils.getNames(cpLeft.getVariables()));
        freshNames.lockNames(CollectionUtils.getNames(cpRight.getVariables()));

        for(int i = 0; i < limit; i++) {
            // rewrite only those terms which have not been rewritten yet
            for(final TRSTerm leftNewTerm : leftNewTerms) {
                final Set<TRSTerm> leftRewriteTerms = leftNewTerm.rewriteGeneralized(Rls, freshNames);
                for(final TRSTerm leftRewriteTerm : leftRewriteTerms) {
                    count++;
                    if ((count & CriticalPairs.countSteps) != 0) {
                        aborter.checkAbortion();
                    }
                    if(leftAllTerms.add(leftRewriteTerm)) {
                        if (i >= start && rightAllTerms.contains(leftRewriteTerm)) {
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
            for(final TRSTerm rightNewTerm : rightNewTerms) {
                final Set<TRSTerm> rightRewriteTerms = rightNewTerm.rewriteGeneralized(Rls, freshNames);
                for(final TRSTerm rightRewriteTerm : rightRewriteTerms) {
                    if ((count & CriticalPairs.countSteps) != 0) {
                        aborter.checkAbortion();
                    }
                    if(rightAllTerms.add(rightRewriteTerm)) {
                        if (i >= start && leftAllTerms.contains(rightRewriteTerm)) {
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
            if(leftNewTerms.isEmpty() && rightNewTerms.isEmpty()) {
                return YNM.NO; // the terms are not joinable independent of limit.
            }

        }

        // the terms are not joinable in limit steps
        return YNM.MAYBE;
    }

}
