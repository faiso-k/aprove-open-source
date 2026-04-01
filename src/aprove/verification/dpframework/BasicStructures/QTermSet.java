/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

public final class QTermSet implements SimpleQTermSet, Immutable, HasTRSTerms, XMLObligationExportable, CPFAdditional {


    // a lookup map that determines to each FunctionSymbol the corresponding rules
    // that have this function symbol. Moreover, a distinction between linear and
    // non-linear rules is made (then one can use the faster linearMatch for linear
    // rules)
    private final Map<FunctionSymbol, Pair<LinkedHashSet<TRSFunctionApplication>, LinkedHashSet<TRSFunctionApplication>>> defSymbolsToLhs;

    // the set of all Lhss
    private final ImmutableSet<TRSFunctionApplication> allLhs;

    private final boolean isEmpty;

    private volatile ImmutableSet<FunctionSymbol> signature;

    public QTermSet(final Iterable<TRSFunctionApplication> lhss) {

        this.defSymbolsToLhs = new LinkedHashMap<FunctionSymbol, Pair<LinkedHashSet<TRSFunctionApplication>, LinkedHashSet<TRSFunctionApplication>>>();
        final Set<TRSFunctionApplication> allLhs = new LinkedHashSet<TRSFunctionApplication>();

        for (final TRSFunctionApplication q : lhss) {
            this.addQ(allLhs, q);
        }
        this.allLhs = ImmutableCreator.create(allLhs);
        this.isEmpty = this.allLhs.isEmpty();
        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.allLhs);
        this.signature = ImmutableCreator.create(signature);

    }

    private void addQ(final Set<TRSFunctionApplication> allLhs, TRSFunctionApplication q) {
        q = (TRSFunctionApplication) q.getStandardRenumbered();

        // do we have q already?
        if (allLhs.contains(q)) {
            return;
        }

        // check whether q is needed (it contains no redex of our previous terms)
        for (final TRSFunctionApplication subTerm : q.getNonVariableSubTerms()) {
            final Pair<? extends Set<TRSFunctionApplication>, ? extends Set<TRSFunctionApplication>> linearNonLinear = this.defSymbolsToLhs.get(subTerm.getRootSymbol());
            if (linearNonLinear != null) {
                for (final TRSFunctionApplication linear : linearNonLinear.x) {
                    if (linear.linearMatches(subTerm)) {
                        return;
                    }
                }
                for (final TRSFunctionApplication nonLinear : linearNonLinear.y) {
                    if (nonLinear.matches(subTerm)) {
                        return;
                    }
                }
            }
        }


        // okay, so we need q. Let us now see whether some old lhss can be thrown out
        final boolean linear = q.isLinear();
        final FunctionSymbol f = q.getRootSymbol();

        final Iterator<Map.Entry<FunctionSymbol, Pair<LinkedHashSet<TRSFunctionApplication>, LinkedHashSet<TRSFunctionApplication>>>> mapIterator = this.defSymbolsToLhs.entrySet().iterator();

        while (mapIterator.hasNext()) {
            final Map.Entry<FunctionSymbol, Pair<LinkedHashSet<TRSFunctionApplication>, LinkedHashSet<TRSFunctionApplication>>> entry = mapIterator.next();
            final Pair<? extends Set<TRSFunctionApplication>, ? extends Set<TRSFunctionApplication>> linearNonLinear = entry.getValue();
            Iterator<TRSFunctionApplication> oldLhsIterator;

            oldLhsIterator = linearNonLinear.x.iterator();
            while (oldLhsIterator.hasNext()) {
                final TRSFunctionApplication oldLhs = oldLhsIterator.next();
                final boolean rewrite = linear ? QTermSet.canBeRewrittenLinear(oldLhs, q) : QTermSet.canBeRewrittenNonLinear(oldLhs, q, f);
                if (rewrite) {
                    oldLhsIterator.remove();
                    allLhs.remove(oldLhs);
                }
            }

            oldLhsIterator = linearNonLinear.y.iterator();
            while (oldLhsIterator.hasNext()) {
                final TRSFunctionApplication oldLhs = oldLhsIterator.next();
                final boolean rewrite = linear ? QTermSet.canBeRewrittenLinear(oldLhs, q) : QTermSet.canBeRewrittenNonLinear(oldLhs, q, f);
                if (rewrite) {
                    oldLhsIterator.remove();
                    allLhs.remove(oldLhs);
                }
            }

            // check whether we have to remove this entry
            if (linearNonLinear.x.isEmpty() && linearNonLinear.y.isEmpty() && !f.equals(entry.getKey())) {
                mapIterator.remove();
            }
        }

        // finally add q
        Pair<LinkedHashSet<TRSFunctionApplication>, LinkedHashSet<TRSFunctionApplication>> pair = this.defSymbolsToLhs.get(f);
        if (pair == null) {
            pair = new Pair<LinkedHashSet<TRSFunctionApplication>, LinkedHashSet<TRSFunctionApplication>>(new LinkedHashSet<TRSFunctionApplication>(), new LinkedHashSet<TRSFunctionApplication>());
            this.defSymbolsToLhs.put(f, pair);
        }

        if (linear) {
            pair.x.add(q);
        } else {
            pair.y.add(q);
        }
        allLhs.add(q);
    }

    private static boolean canBeRewrittenLinear(final TRSFunctionApplication t, final TRSFunctionApplication lhsQ) {
        assert(lhsQ.isLinear());
        for (final TRSFunctionApplication subTerm : t.getNonVariableSubTerms()) {
            if (lhsQ.linearMatches(subTerm)) {
                return true;
            }
        }
        return false;
    }

    private static boolean canBeRewrittenNonLinear(final TRSFunctionApplication t, final TRSFunctionApplication lhsQ, final FunctionSymbol f) {
        assert(!lhsQ.isLinear());
        for (final TRSFunctionApplication subTerm : t.getNonVariableSubTerms()) {
            if (subTerm.getRootSymbol().equals(f) && lhsQ.matches(subTerm)) {
                return true;
            }
        }
        return false;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
//        if (this.signature == null) {
//            synchronized(this) {
//                if (this.signature == null) {
//                    Set<FunctionSymbol> signature = Collections.getFunctionSymbols(this.allLhs);
//                    this.signature = ImmutableCreator.create(signature);
//                }
//            }
//        }
        return this.signature;
    }

    /**
     * returns the set of all needed lhss where variables start with STANDARD_PREFIX
     */
    @Override
    public ImmutableSet<TRSFunctionApplication> getTerms() {
        return this.allLhs;
    }

    public boolean isEmpty() {
        return this.isEmpty;
    }

    @Override
    public boolean canAllLhsBeRewritten(final Set<? extends HasLHS> R) {
        if (R.isEmpty()) {
            return true;
        }
        if (this.isEmpty) {
            return false;
        }

        for (final HasLHS rule : R) {
            if (!this.canBeRewrittenWithNonEmptyQ(rule.getLeft())) {
                return false;
            }
        }
        return true;
    }

    /**
     * checks whether all terms in the collection can be rewritten
     * @param lhsR
     * @return
     */
    @Override
    public boolean canAllBeRewritten(final Collection<TRSFunctionApplication> terms) {
        if (terms.isEmpty()) {
            return true;
        }
        if (this.isEmpty) {
            return false;
        }

        for (final TRSTerm t : terms) {
            if (!this.canBeRewrittenWithNonEmptyQ(t)) {
                return false;
            }
        }
        return true;
    }

    /**
     * checks whether t can be rewritten
     * @param t
     */
    @Override
    public boolean canBeRewritten(final TRSTerm t) {
        if (this.isEmpty) {
            return false;
        }
        return this.canBeRewrittenWithNonEmptyQ(t);
    }


    private boolean canBeRewrittenWithNonEmptyQ(TRSTerm t) {
        if (Globals.useAssertions) {
            assert(!this.isEmpty);
        }
        t = t.getStandardRenumbered();

        /*
         * perhaps also use some cache for all terms tested (limited cache?)
         */

        if (this.allLhs.contains(t)) {
            return true;
        }

        for (final TRSFunctionApplication subTerm : t.getNonVariableSubTerms()) {
            final Pair<? extends Set<TRSFunctionApplication>, ? extends Set<TRSFunctionApplication>> linearNonLinear = this.defSymbolsToLhs.get(subTerm.getRootSymbol());
            if (linearNonLinear != null) {
                for (final TRSFunctionApplication linear : linearNonLinear.x) {
                    if (linear.linearMatches(subTerm)) {
                        return true;
                    }
                }
                for (final TRSFunctionApplication nonLinear : linearNonLinear.y) {
                    if (nonLinear.matches(subTerm)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    @Override
    public boolean canBeRewrittenAtRoot(final TRSFunctionApplication t) {
        final Pair<? extends Set<TRSFunctionApplication>, ? extends Set<TRSFunctionApplication>> linearNonLinear = this.defSymbolsToLhs.get(t.getRootSymbol());
        if (linearNonLinear != null) {
            for (final TRSFunctionApplication linear : linearNonLinear.x) {
                if (linear.linearMatches(t)) {
                    return true;
                }
            }
            for (final TRSFunctionApplication nonLinear : linearNonLinear.y) {
                if (nonLinear.matches(t)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * checks whether some term of terms can be rewritten
     * @param terms
     */
    @Override
    public boolean someTermCanBeRewritten(final Iterable<? extends TRSTerm> terms) {
        if (this.isEmpty) {
            return false;
        }
        for (final TRSTerm t : terms) {
            if (this.canBeRewrittenWithNonEmptyQ(t)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether some proper subterm of <code>t</code> can be rewritten
     */
    @Override
    public boolean canBeRewrittenBelowRoot(final TRSTerm t){
        if (t.isVariable()) {
            return false;
        }
        return this.someTermCanBeRewritten(((TRSFunctionApplication) t).getArguments());
    }

    @Override
    public boolean equals(final Object other) {
        if(this == other) {
            return true;
        }
        if(other instanceof QTermSet) {
            return this.allLhs.equals(((QTermSet) other).allLhs);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.allLhs.hashCode() * 246813579;
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.QTERMSET.createElement(doc);
        CollectionUtils.addChildren(this.allLhs, e, doc, xmlMetaData);
        return e;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = CPFTag.INNERMOST_LHSS.createElement(doc);
        for (final TRSFunctionApplication fApp : this.allLhs) {
            e.appendChild(fApp.toCPF2(doc, xmlMetaData));
        }
        return e;
    }

}
