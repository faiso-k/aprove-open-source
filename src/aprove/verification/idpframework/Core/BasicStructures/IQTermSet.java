/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Algorithms.Matching.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class IQTermSet implements Immutable, SimpleQTermSet, IDPExportable {

    public static enum PredefinedQMode {

        PredefinedRule, ConstructorRewriting;

    }

    // a lookup map that determines to each IFunctionSymbol<?> the corresponding rules
    // that have this function symbol. Moreover, a distinction between linear and
    // non-linear rules is made (then one can use the faster linearMatch for linear
    // rules)
    private final Map<IFunctionSymbol<?>, Pair<LinkedHashSet<IFunctionApplication<?>>, LinkedHashSet<IFunctionApplication<?>>>> defSymbolsToLhs;

    // the set of all Lhss
    private final ImmutableSet<IFunctionApplication<?>> allLhs;

    private final boolean hasNoUserDefinedRules;
    private final int hashCode;

    private volatile ImmutableSet<IFunctionSymbol<?>> signature;

    private final IDPPredefinedMap predefinedMap;

    private final PredefinedQMode predefinedMode;

    private final PositionalMatchUnification<Unused> fastMatching;

    public IQTermSet(final Iterable<IFunctionApplication<?>> lhss, final PredefinedQMode predefinedMode,
        final IDPPredefinedMap predefinedMap) {

        this.predefinedMode = predefinedMode;

        this.defSymbolsToLhs =
            new LinkedHashMap<IFunctionSymbol<?>, Pair<LinkedHashSet<IFunctionApplication<?>>, LinkedHashSet<IFunctionApplication<?>>>>();
        final Set<IFunctionApplication<?>> allLhs =
            new LinkedHashSet<IFunctionApplication<?>>();

        for (final IFunctionApplication<?> q : lhss) {
            this.addQ(allLhs, q);
        }

        this.allLhs = ImmutableCreator.create(allLhs);
        this.hasNoUserDefinedRules = this.allLhs.isEmpty();
        final Set<IFunctionSymbol<?>> signature =
            new LinkedHashSet<IFunctionSymbol<?>>();
        for (final ITerm<?> lhs : this.allLhs) {
            lhs.collectFunctionSymbols(signature);
        }
        this.predefinedMap = predefinedMap;
        this.signature = ImmutableCreator.create(signature);

        final Map<ITerm<?>, Unused> mappedLhss = new LinkedHashMap<ITerm<?>, Unused>();
        for (final IFunctionApplication<?> lhs : allLhs) {
            mappedLhss.put(lhs, null);
        }

        this.fastMatching = new PositionalMatchUnification<Unused>(mappedLhss);

        this.hashCode =
            this.allLhs.hashCode() * 246813579 + predefinedMap.hashCode() * 31 + predefinedMode.hashCode() * 11;
    }

    private void addQ(final Set<IFunctionApplication<?>> allLhs,
        final IFunctionApplication<?> q) {
        // do we have q already?
        if (allLhs.contains(q)) {
            return;
        }

        // check whether q is needed (it contains no redex of our previous terms)
        for (final IFunctionApplication<?> subTerm : q.getNonVariableSubTerms()) {
            final Pair<? extends Set<IFunctionApplication<?>>, ? extends Set<IFunctionApplication<?>>> linearNonLinear =
                this.defSymbolsToLhs.get(subTerm.getRootSymbol());
            if (linearNonLinear != null) {
                for (final IFunctionApplication<?> linear : linearNonLinear.x) {
                    if (linear.linearMatches(subTerm)) {
                        return;
                    }
                }
                for (final IFunctionApplication<?> nonLinear : linearNonLinear.y) {
                    if (nonLinear.matches(subTerm)) {
                        return;
                    }
                }
            }
        }

        // okay, so we need q. Let us now see whether some old lhss can be thrown out
        final boolean linear = q.isLinear();
        final IFunctionSymbol<?> f = q.getRootSymbol();

        final Iterator<Map.Entry<IFunctionSymbol<?>, Pair<LinkedHashSet<IFunctionApplication<?>>, LinkedHashSet<IFunctionApplication<?>>>>> mapIterator =
            this.defSymbolsToLhs.entrySet().iterator();

        while (mapIterator.hasNext()) {
            final Map.Entry<IFunctionSymbol<?>, Pair<LinkedHashSet<IFunctionApplication<?>>, LinkedHashSet<IFunctionApplication<?>>>> entry =
                mapIterator.next();
            final Pair<? extends Set<IFunctionApplication<?>>, ? extends Set<IFunctionApplication<?>>> linearNonLinear =
                entry.getValue();
            Iterator<IFunctionApplication<?>> oldLhsIterator;

            oldLhsIterator = linearNonLinear.x.iterator();
            while (oldLhsIterator.hasNext()) {
                final IFunctionApplication<?> oldLhs = oldLhsIterator.next();
                final boolean rewrite =
                    linear ? IQTermSet.canBeRewrittenLinear(oldLhs, q)
                        : IQTermSet.canBeRewrittenNonLinear(oldLhs, q, f);
                    if (rewrite) {
                        oldLhsIterator.remove();
                        allLhs.remove(oldLhs);
                    }
            }

            oldLhsIterator = linearNonLinear.y.iterator();
            while (oldLhsIterator.hasNext()) {
                final IFunctionApplication<?> oldLhs = oldLhsIterator.next();
                final boolean rewrite =
                    linear ? IQTermSet.canBeRewrittenLinear(oldLhs, q)
                        : IQTermSet.canBeRewrittenNonLinear(oldLhs, q, f);
                    if (rewrite) {
                        oldLhsIterator.remove();
                        allLhs.remove(oldLhs);
                    }
            }

            // check whether we have to remove this entry
            if (linearNonLinear.x.isEmpty() && linearNonLinear.y.isEmpty()
                    && !f.equals(entry.getKey())) {
                mapIterator.remove();
            }
        }

        // finally add q
        Pair<LinkedHashSet<IFunctionApplication<?>>, LinkedHashSet<IFunctionApplication<?>>> pair =
            this.defSymbolsToLhs.get(f);
        if (pair == null) {
            pair =
                new Pair<LinkedHashSet<IFunctionApplication<?>>, LinkedHashSet<IFunctionApplication<?>>>(
                        new LinkedHashSet<IFunctionApplication<?>>(),
                        new LinkedHashSet<IFunctionApplication<?>>());
            this.defSymbolsToLhs.put(f, pair);
        }

        if (linear) {
            pair.x.add(q);
        } else {
            pair.y.add(q);
        }
        allLhs.add(q);
    }

    private static boolean canBeRewrittenLinear(final IFunctionApplication<?> t,
        final IFunctionApplication<?> lhsQ) {
        assert (lhsQ.isLinear());

        for (final IFunctionApplication<?> subTerm : t.getNonVariableSubTerms()) {
            if (lhsQ.linearMatches(subTerm)) {
                return true;
            }
        }
        return false;
    }

    private static boolean canBeRewrittenNonLinear(final IFunctionApplication<?> t,
        final IFunctionApplication<?> lhsQ,
        final IFunctionSymbol<?> f) {
        assert (!lhsQ.isLinear());
        for (final IFunctionApplication<?> subTerm : t.getNonVariableSubTerms()) {
            if (subTerm.getRootSymbol().equals(f) && lhsQ.matches(subTerm)) {
                return true;
            }
        }
        return false;
    }

    public ImmutableSet<IFunctionSymbol<?>> getUserDefinedSignature() {
        //        if (this.signature == null) {
        //            synchronized(this) {
        //                if (this.signature == null) {
        //                    Set<IFunctionSymbol<?>> signature = Collections.getFunctionSymbols(this.allLhs);
        //                    this.signature = ImmutableCreator.create(signature);
        //                }
        //            }
        //        }
        return this.signature;
    }

    /**
     * returns the set of all needed lhss where variables start with
     * STANDARD_PREFIX
     */
    public ImmutableSet<IFunctionApplication<?>> getUserDefinedTerms() {
        return this.allLhs;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#canAllLhsBeRewritten(java.util.Set)
     */
    @Override
    public boolean canAllLhsBeRewritten(final Set<? extends IRule> R) {
        if (R.isEmpty()) {
            return true;
        }

        for (final IRule rule : R) {
            if (!this.canBeRewritten(rule.getLeft().renumberVariables(ITerm.SECOND_STANDARD_PREFIX))) {
                return false;
            }
        }
        return true;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#canAllBeRewritten(java.util.Collection)
     */
    @Override
    public boolean canAllBeRewritten(final Collection<? extends ITerm<?>> terms) {
        if (terms.isEmpty()) {
            return true;
        }

        for (final ITerm<?> t : terms) {
            if (!this.canBeRewritten(t)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean canBeRewritten(final ITerm<?> t) {
        /*
         * perhaps also use some cache for all terms tested (limited cache?)
         */
        if (!this.hasNoUserDefinedRules) {
            final CollectionMap<IPosition, TermMatchUnif<Unused>> fastMatches = this.fastMatching.getMatchesToTerm(t);
            final boolean fastMatchingResult = !fastMatches.isEmpty();

            if (fastMatchingResult) {
                return true;
            }
        }

        for (final IFunctionApplication<?> subTerm : t.getNonVariableSubTerms()) {
            final PredefinedFunction<?, ?> func =
                PredefinedUtil.getPredefinedFunction(subTerm.getRootSymbol());
            if (func != null
                && ((this.predefinedMode == PredefinedQMode.PredefinedRule && func.isPredefLhs(subTerm)) || (this.predefinedMode == PredefinedQMode.ConstructorRewriting && func.canMatchPredefLhs(subTerm)))) {
                return true;
            }
        }

        return false;
//
//        if (this.allLhs.contains(t)) {
//            assert fastMatches.containsKey(IPosition.create());
//            return true;
//        }
//
//        for (final IFunctionApplication<?> subTerm : t.getNonVariableSubTerms()) {
//            final PredefinedFunction<?, ?> func =
//                PredefinedUtil.getPredefinedFunction(subTerm.getRootSymbol());
//            if (func != null &&
//                    ((this.predefinedMode == PredefinedQMode.PredefinedRule && func.isPredefLhs(subTerm)) ||
//                            (this.predefinedMode == PredefinedQMode.ConstructorRewriting && func.canMatchPredefLhs(subTerm)))) {
//                return true;
//            }
//
//            final Pair<? extends Set<IFunctionApplication<?>>, ? extends Set<IFunctionApplication<?>>> linearNonLinear =
//                this.defSymbolsToLhs.get(subTerm.getRootSymbol());
//            if (linearNonLinear != null) {
//                for (final IFunctionApplication<?> linear : linearNonLinear.x) {
//                    if (linear.linearMatches(subTerm)) {
//                        if (!fastMatchingResult) {
//                            fastMatches = fastMatching.getMatchesToTerm(t);
//                        }
//                        assert fastMatchingResult : "fast matching invalid";
//                        return true;
//                    }
//                }
//                for (final IFunctionApplication<?> nonLinear : linearNonLinear.y) {
//                    if (nonLinear.matches(subTerm)) {
//                        assert fastMatchingResult : "fast matching invalid";
//                        return true;
//                    }
//                }
//            }
//        }
//        assert !fastMatchingResult : "fast matching invalid";
//        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#canBeRewrittenAtRoot(aprove.verification.dpframework.BasicStructures.IFunctionApplication<?>)
     */
    @Override
    public boolean canBeRewrittenAtRoot(final IFunctionApplication<?> t) {
        final Pair<? extends Set<IFunctionApplication<?>>, ? extends Set<IFunctionApplication<?>>> linearNonLinear =
            this.defSymbolsToLhs.get(t.getRootSymbol());
        if (linearNonLinear != null) {
            for (final IFunctionApplication<?> linear : linearNonLinear.x) {
                if (linear.linearMatches(t)) {
                    return true;
                }
            }
            for (final IFunctionApplication<?> nonLinear : linearNonLinear.y) {
                if (nonLinear.matches(t)) {
                    return true;
                }
            }
        }
        final PredefinedFunction<?, ?> func =
            PredefinedUtil.getPredefinedFunction(t.getRootSymbol());
        if (func != null && func.isPredefLhs(t)) {
            return true;
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#someTermCanBeRewritten(java.lang.Iterable)
     */
    @Override
    public boolean someTermCanBeRewritten(final Iterable<? extends ITerm<?>> terms) {
        for (final ITerm<?> t : terms) {
            if (this.canBeRewritten(t)) {
                return true;
            }
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#canBeRewrittenBelowRoot(aprove.verification.dpframework.BasicStructures.ITerm<?>)
     */
    @Override
    public boolean canBeRewrittenBelowRoot(final ITerm<?> t) {
        if (t.isVariable()) {
            return false;
        }
        return this.someTermCanBeRewritten(((IFunctionApplication<?>) t).getArguments());
    }

    public IDPPredefinedMap getPredefinedMap() {
        return this.predefinedMap;
    }

    public PredefinedQMode getPredefinedMode() {
        return this.predefinedMode;
    }

    /**
     * checks whether t can be rewritten
     * @param t
     */
    public boolean canAlwaysRewritteAnArgUnifiedPredefLhs(final IFunctionApplication<?> t) {
        for (final ITerm<?> arg : t.getArguments()) {
            if (!arg.isVariable()) {
                final PredefinedFunction<?, ?> func =
                    PredefinedUtil.getPredefinedFunction(((IFunctionApplication<?>) arg).getRootSymbol());
                if (func != null && func.canMatchPredefLhs(arg)) {
                    return true;
                }
            }
        }
        return false;
    }

    public static IQTermSet createConstructorQ(final Collection<IRule> rules, final IDPPredefinedMap predefinedMap) {
        final Set<IFunctionApplication<?>> qTerms = new LinkedHashSet<IFunctionApplication<?>>();
        for (final IRule rule : rules) {
            final IFunctionSymbol<?> fs = rule.getLeft().getRootSymbol();
            final ArrayList<ITerm<?>> arguments = new ArrayList<ITerm<?>>(fs.getArity());

            for (int i = 0; i < fs.getArity(); i++) {
                arguments.add(ITerm.createVariable("x_" + i, DomainFactory.UNKNOWN));
            }

            qTerms.add(ITerm.createFunctionApplication(fs, arguments));
        }
        return new IQTermSet(qTerms, PredefinedQMode.ConstructorRewriting, predefinedMap);
    }

    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof IQTermSet) {
            final IQTermSet qOther = (IQTermSet) other;
            return this.hashCode == qOther.hashCode
            && this.allLhs.equals(qOther.allLhs)
            && this.predefinedMap.equals(qOther.predefinedMap)
            && this.predefinedMode.equals(qOther.predefinedMode);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public final String export(final Export_Util o) {
        return this.export(o, IDPExportable.DEFAULT_LEVEL);
    }

    @Override
    public final String export(final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final StringBuilder sb = new StringBuilder();
        this.export(sb, o, verbosityLevel);
        return sb.toString();
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        sb.append(o.set(this.allLhs, Export_Util.SIMPLESET));
    }
}
