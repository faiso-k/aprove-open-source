package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * This class represents argument filtering systems as a map
 * from function symbols to a list of YNM where
 * <ul>
 * <li> Y indicates the presence of the argument
 * <li> N indicates the absence of the argument
 * <li> M indicates that we do not care about the presence of the argument
 * </ul>
 * A function symbol for which at least one argument is marked M
 * is called ambiguous. An argument filtering is called ambiguous
 * if it contains an ambigous function symbol.
 * Furthermore, for an unambiguous function symbol with only one Y
 * a boolean flag collapsing indicates whether the function symbol
 * is to be collapsed or to be kept.
 *
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class Afs
    implements
        QActiveCondition.Afs,
        HasFunctionSymbols,
        Exportable,
        HTML_Able,
        PLAIN_Able,
        CPFAdditional
{

    protected Map<FunctionSymbol,Filtering> filters;
    protected BidirectionalMap<FunctionSymbol, FunctionSymbol> symbolMap;

    public Afs() {
        this.filters = new LinkedHashMap<FunctionSymbol,Filtering>();
    }

    public Afs(final Afs old) {
        this.filters = new LinkedHashMap<FunctionSymbol,Filtering>(old.filters);
    }

    /**
     * returns all filters,
     * the boolean indicates a collapsing value.
     * Do not modify the returned YNM-Maps!
     * @return
     */
    public Iterable<Triple<FunctionSymbol, YNM[], Boolean>> getFilterings() {
        return new Iterable<Triple<FunctionSymbol, YNM[], Boolean>>() {
            @Override
            public Iterator<Triple<FunctionSymbol, YNM[], Boolean>> iterator() {
                final Iterator<Map.Entry<FunctionSymbol, Filtering>> i = Afs.this.filters.entrySet().iterator();
                return new Iterator<Triple<FunctionSymbol, YNM[], Boolean>>() {
                    @Override
                    public boolean hasNext() {
                        return i.hasNext();
                    }
                    @Override
                    public Triple<FunctionSymbol, YNM[], Boolean> next() {
                        final Map.Entry<FunctionSymbol, Filtering> mapping = i.next();
                        final Filtering filter = mapping.getValue();
                        return new Triple<FunctionSymbol, YNM[], Boolean>(
                                mapping.getKey(),
                                filter.x,
                                filter.y
                                );
                    }
                    @Override
                    public void remove() {
                        throw new UnsupportedOperationException();
                    }
                };
            }
        };
    }

    @Override
    public ImmutableSet<FunctionSymbol> getFunctionSymbols() {
        return ImmutableCreator.create(this.filters.keySet());
    }

    public static Pair<YNM[], Boolean> getNoFiltering(final int arity) {
        final YNM[] args = new YNM[arity];
        for (int i = 0; i < arity; i++) {
            args[i] = YNM.YES;
        }
        return new Pair<>(args,false);
    }

    public void setNoFiltering(final FunctionSymbol f) {
        assert(f != null);
        this.setFiltering(f, Afs.getNoFiltering(f.getArity()));
    }

    public void setCollapsing(final FunctionSymbol f, final int pos) {
        if (Globals.useAssertions) {
            assert(f != null);
            assert(pos >= 0);
        }
        final int arity = f.getArity();
        if (Globals.useAssertions) {
            assert(pos < arity);
        }
        final YNM[] args = new YNM[arity];
        for (int i = 0; i < pos; i++) {
            args[i] = YNM.NO;
        }
        args[pos] = YNM.YES;
        for (int i = pos+1; i < arity; i++) {
            args[i] = YNM.NO;
        }
        this.setFiltering(f, args, true);
    }


    public void setFiltering(final FunctionSymbol f, final Pair<YNM[], Boolean> filter) {
        this.setFiltering(f, filter.x, filter.y);
    }

    public Pair<YNM[], Boolean> getFiltering(final FunctionSymbol f) {
        final Filtering filter = this.filters.get(f);
        return new Pair<YNM[], Boolean>(filter.x, filter.y);
    }


    public void removeFiltering(final FunctionSymbol f) {
        this.filters.remove(f);
    }

    public void setFiltering(final Afs afs) {
        this.filters.putAll(afs.filters);
    }

    public void setFiltering(final FunctionSymbol f, final boolean[] args) {
        final int arity = f.getArity();
        final YNM[] pattern = new YNM[arity];
        for (int i = 0; i < arity; i++) {
            pattern[i] = args[i] ? YNM.YES : YNM.NO;
        }
        this.setFiltering(f, pattern, false);
    }

    public void setFiltering(final FunctionSymbol f, final YNM[] args) {
        if (Globals.useAssertions) {
            assert(f != null);
            assert(args != null);
            assert(f.getArity() == args.length);
        }
        this.setFiltering(f, args, false);
    }

    public boolean[] getRegardedArgs(final FunctionSymbol f) {
        assert(f != null);
        assert(this.filters.get(f) == null || Afs.countMAYBE(this.filters.get(f).x) == 0);
        final Filtering filtering = this.filters.get(f);
        final boolean[] regarded = new boolean[f.getArity()];
        if (filtering == null) {
            Arrays.fill(regarded,true);
        } else {
            final YNM[] args = this.filters.get(f).x;
            for (int i = 0; i < f.getArity(); i++) {
                regarded[i] = args[i] == YNM.YES;
            }
        }
        return regarded;
    }

    public List<Boolean> getRegardedArgsAsList(final FunctionSymbol f) {
        assert(f != null);
        assert(this.filters.get(f) == null || Afs.countMAYBE(this.filters.get(f).x) == 0);
        final Filtering filtering = this.filters.get(f);
        final List<Boolean> regarded = new ArrayList<Boolean>(f.getArity());
        if (filtering == null) {
            for (int i = 0; i < f.getArity(); i++) {
                regarded.add(true);
            }
        } else {
            final YNM[] args = this.filters.get(f).x;
            for (int i = 0; i < f.getArity(); i++) {
                regarded.add(args[i] == YNM.YES);
            }
        }
        return regarded;
    }

    private void setFiltering(final FunctionSymbol f, final YNM[] args, final boolean collapsing) {
// ?        assert(!collapsing || (this.countYES(args) == 1 && this.countMAYBE(args) == 0));
        this.filters.put(f, new Filtering(args, collapsing));
    }

    private static int countYES(final YNM[] args) {
        int card = 0;
        for (final YNM arg : args) {
            if (arg == YNM.YES) {
                card++;
            }
        }
        return card;
    }

    private static int countMAYBE(final YNM[] args) {
        int card = 0;
        for (final YNM arg : args) {
            if (arg == YNM.MAYBE) {
                card++;
            }
        }
        return card;
    }

    private static boolean isAmbiguous(final YNM[] args) {
        assert(args != null);
        for (final YNM arg : args) {
            if (arg == YNM.MAYBE) {
                return true;
            }
        }
        return false;
    }

    public boolean isEmpty() {
        for (final Map.Entry<FunctionSymbol,Filtering> f : this.filters.entrySet()) {
            for (final YNM entry : f.getValue().x) {
                if (entry != YNM.YES) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * doku guess by andrej:
     * This function results YNM.YES if this is a refinement of other.
     * Here, \pi_1 is a refinement of \pi_2 iff \pi_1(f) \subseteeq \pi_2(f)
     * for all symbols f, i.e., \pi_1 filters more arguments of f than pi_2.
     * [Static Termination Analysis for Prolog using Term Rewriting and SAT Solving,
     *  Schneider-Kamp 2008]
     *
     * Otherwise YNM.NO, or YNM.MAYBE whenever one filtering has YNM.MAYBE.
     *
     * Note:
     *  1. If this is undefined for one function symbol f, but other is defined
     *     for f, then we assume this filteres nothing, i.e., this(f) = [YES,...,YES]
     *  2. this method does not handle collapsing Afs
     */
    public YNM isRefinementOf(final Afs other) {
        for(final Map.Entry<FunctionSymbol, Filtering> filtering : other.filters.entrySet()) {
            final YNM[] right = filtering.getValue().x;
            YNM[] left;
            if( this.hasFilter(filtering.getKey()) ) {
                left = this.filters.get(filtering.getKey()).x;
            } else {
                left = new YNM[filtering.getKey().getArity()];
                for(int i = 0; i < filtering.getKey().getArity(); ++i) {
                    left[i] = YNM.YES;
                }
            }

            if (left.length != right.length) {
                return YNM.NO;
            }

            for (int i = 0; i < left.length; i++) {
                switch (right[i]) {
                    case MAYBE:
                        switch (left[i]) {
                            case YES:
                            case MAYBE: return YNM.MAYBE;
                        }
                        break;
                    case NO:
                        switch (left[i]) {
                            case YES:   return YNM.NO;
                            case MAYBE: return YNM.MAYBE;
                        }
                }
            }
        }
        return YNM.YES;
    }

    public boolean isAmbiguous(final FunctionSymbol f) {
        assert(f != null);
        return Afs.isAmbiguous(this.filters.get(f).x);
    }

    public boolean isAmbiguous() {
        for (final FunctionSymbol f : this.filters.keySet()) {
            if (this.isAmbiguous(f)) {
                return true;
            }
        }
        return false;
    }

    /**
     * returns a YNM, whether the function f filters its
     * argument at the given position
     * @param f
     * @param position
     * @return
     */
    @Override
    public YNM filterPosition(final FunctionSymbol f, final int position) {
        final Filtering filter = this.filters.get(f);
        if (filter == null) {
            return YNM.MAYBE;
        } else {
            return filter.x[position];
        }
    }

    /**
     * returns a YNM whether the filter filters away a certain position in t
     */
    public YNM filterPosition(final TRSTerm t, final Position position) {
        if (Globals.useAssertions) {
            assert t != null && position != null;
            assert t.getPositions().contains(position);
        }

        if (position.getDepth() == 0) {
            return YNM.YES;
        } else if (position.getDepth() == 1) {
            return this.filterPosition(
                ((TRSFunctionApplication) t).getRootSymbol(),
                position.firstIndex());
        } else {
            if (this.filterPosition(((TRSFunctionApplication) t).getRootSymbol(),
                position.firstIndex()) == YNM.NO) {
                return YNM.NO;
            } else {
                return this.filterPosition(
                    t.getSubterm(Position.create(position.firstIndex())),
                    position.tail(1));
            }
        }
    }

    public TRSTerm filterTerm(final TRSTerm t) {
        if (t.isVariable()) {
            return t;
        } else {
            final TRSFunctionApplication fapp = (TRSFunctionApplication) t;
            final FunctionSymbol f = fapp.getRootSymbol();
            final Filtering filtering = this.filters.get(f);
            if (filtering == null) {
                final ImmutableList<? extends TRSTerm> args = fapp.getArguments();
                final int size = args.size();
                final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(size);
                for (int i = 0; i < size; i++) {
                    newArgs.add(this.filterTerm(args.get(i)));
                }
                final FunctionSymbol newF = this.getFilteredSymbol(f, size);
                return TRSTerm.createFunctionApplication(newF, ImmutableCreator.create(newArgs));
            }
            if (Globals.useAssertions) {
                assert(Afs.countMAYBE(filtering.x) == 0);
            }
            final ImmutableList<? extends TRSTerm> args = fapp.getArguments();
            final int size = args.size();
            if (filtering.y) { // collapsing case
                if (Globals.useAssertions) {
                    assert(Afs.countYES(filtering.x) == 1);
                }
                for (int i = 0; i < size; i++) {
                    final YNM filter = filtering.x[i];
                    if (filter == YNM.YES) {
                        return this.filterTerm(args.get(i));
                    }
                }
                assert(false);
            }
            final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(size >> 1);
            for (int i = 0; i < size; i++) {
                final YNM filter = filtering.x[i];
                if (filter == YNM.YES) {
                    newArgs.add(this.filterTerm(args.get(i)));
                }
            }
            if (Globals.useAssertions) {
                assert(newArgs.size() == Afs.countYES(filtering.x));
            }
            final FunctionSymbol newF = this.getFilteredSymbol(f,newArgs.size());
            return TRSTerm.createFunctionApplication(newF, ImmutableCreator.create(newArgs));
        }
    }

    public Set<Constraint<TRSTerm>> filterConstraints(final Set<Constraint<TRSTerm>> cs) {
        final Set<Constraint<TRSTerm>> result = new LinkedHashSet<Constraint<TRSTerm>>();
        for (final Constraint<TRSTerm> c : cs) {
            result.add(this.filterConstraint(c));
        }
        return result;
    }

    public Constraint<TRSTerm> filterConstraint(final Constraint<TRSTerm> c) {
        return Constraint.create(this.filterTerm(c.getLeft()) ,this.filterTerm(c.getRight()),c.getType());
    }

    public Set<GeneralizedRule> filterGeneralizedRules(final Set<GeneralizedRule> rules) {
        final Set<GeneralizedRule> result = new LinkedHashSet<GeneralizedRule>();
        for (final GeneralizedRule rule : rules) {
            result.add(this.filterRule(rule));
        }
        return result;
    }

    public GeneralizedRule filterRule(final GeneralizedRule rule) {
        return GeneralizedRule.create((TRSFunctionApplication)this.filterTerm(rule.getLeft()), this.filterTerm(rule.getRight()));
    }

    public Set<Rule> filterRules(final Set<Rule> rules) {
        final Set<Rule> result = new LinkedHashSet<Rule>();
        for (final Rule rule : rules) {
            result.add(this.filterRule(rule));
        }
        return result;
    }

    public Rule filterRule(final Rule rule) {
        return Rule.create((TRSFunctionApplication)this.filterTerm(rule.getLeft()), this.filterTerm(rule.getRight()));
    }

    public Set<Pair<TRSTerm,TRSTerm>> filter(final Set<? extends GeneralizedRule> rules) {
        final Set<Pair<TRSTerm,TRSTerm>> result = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>();
        for (final GeneralizedRule rule : rules) {
            result.add(this.filter(rule));
        }
        return result;
    }

    public Pair<TRSTerm,TRSTerm> filter(final GeneralizedRule rule) {
        return new Pair<TRSTerm,TRSTerm>(this.filterTerm(rule.getLeft()), this.filterTerm(rule.getRight()));
    }

    public Afs addTuples(final Map<FunctionSymbol, FunctionSymbol> defToTup) {
        final Afs result = new Afs();
        result.filters = new LinkedHashMap<FunctionSymbol, Filtering>(this.filters);
        for (final Map.Entry<FunctionSymbol,FunctionSymbol> entry : defToTup.entrySet()) {
            final Filtering filtering = this.filters.get(entry.getKey());
            if (filtering != null) {
                result.filters.put(entry.getValue(),filtering);
            }
        }
        return result;
    }

    public Afs reduceToSignature(final Set<FunctionSymbol> sig) {
        final Afs result = new Afs();
        result.filters = new LinkedHashMap<FunctionSymbol, Filtering>(this.filters);
        result.filters.keySet().retainAll(sig);
        return result;
    }

    /**
     * Intersects this filter with pi and returns the result.
     * Does not regard collapsing! <- TODO
     */
    public Afs intersectWith(final Afs pi) {
        final Afs result = new Afs();
        result.setFiltering(this);
        final Map<FunctionSymbol, Filtering> otherFilters = pi.filters;
        for (final Map.Entry<FunctionSymbol, Filtering> entry : otherFilters.entrySet()) {

            if (result.hasFilter(entry.getKey())) {
                final Pair<YNM[], Boolean> piFiltering =
                    result.getFiltering(entry.getKey());
                final Pair<YNM[], Boolean> otherFiltering = entry.getValue();
                if (result.hasFilter(entry.getKey())) {
                    if (otherFiltering.x.length == piFiltering.x.length
                        && piFiltering.y == false) {
                        for (int i = 0; i < piFiltering.x.length; ++i) {
                            if (piFiltering.x[i] != YNM.NO) {
                                if (otherFiltering.x[i] == YNM.NO) {
                                    result.setFiltering(entry.getKey(), i,
                                        YNM.NO);
                                } else if (otherFiltering.x[i] == YNM.YES
                                    && piFiltering.x[i] == YNM.MAYBE) {
                                    result.setFiltering(entry.getKey(), i,
                                        YNM.YES);
                                }
                            }
                        }
                    }
                } else {
                    result.setFiltering(entry.getKey(), otherFiltering);
                }
            } else {
                result.setFiltering(entry.getKey(), entry.getValue());
            }
        }
        return result;
    }

    @SuppressWarnings("serial")
    private static class Filtering extends Pair<YNM[],Boolean> {
        public Filtering(final YNM[] args, final Boolean collapsing) {
            super(args, collapsing);
        }
    }

    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder();
        for (final Map.Entry<FunctionSymbol,Filtering> entry : this.filters.entrySet()) {
            final FunctionSymbol f = entry.getKey();
            final Filtering filtering = entry.getValue();
            result.append(f.getName()+"/"+f.getArity()+(filtering.y ? ")" : "("));
            for (final YNM arg : filtering.x) {
                result.append(arg+",");
            }
            result.deleteCharAt(result.length()-1);
            result.append((filtering.y ? "(" : ")")+"\n");
        }
        return result.toString();
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toPLAIN() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(final Export_Util o) {
        return this.export(o, 1);
    }
    public String export(final Export_Util o, final int offset) {
        final StringBuilder result = new StringBuilder();
        for (final Map.Entry<FunctionSymbol,Filtering> entry : this.filters.entrySet()) {
            final FunctionSymbol f = entry.getKey();
            final int lArity = f.getArity();
//            if (lArity == 0) {
//                continue;
//            }

            final Filtering filtering = entry.getValue();
            final TRSTerm[] largs = new TRSTerm[lArity];
            final ArrayList<TRSTerm> rargs = new ArrayList<TRSTerm>();
            int rArity = 0;
            for (int i = 0; i < lArity; i++) {
                largs[i] = TRSTerm.createVariable("x"+(i+offset));
                switch (filtering.x[i]) {
                case YES:
                    rargs.add(TRSTerm.createVariable("x"+(i+offset)));
                    rArity++;
                    break;
                case MAYBE:
                    rargs.add(TRSTerm.createFunctionApplication(FunctionSymbol.create("x"+(i+offset),0),TRSTerm.EMPTY_ARGS));
                    rArity++;
                    break;
                }
            }
            final TRSFunctionApplication left = TRSTerm.createFunctionApplication(f,largs);
            result.append(o.export(left)+o.appSpace()+" = "+o.appSpace());
            if (filtering.y) {
                for (int i = 0; i < rArity; i++) {
                    if (i > 0) {
                        result.append(", ");
                    }
                    result.append(o.export(rargs.get(i)));
                }
            } else {
                final TRSFunctionApplication right = TRSTerm.createFunctionApplication(this.getFilteredSymbol(f, rArity),ImmutableCreator.create(rargs));
                result.append(o.export(right));
            }
            result.append(o.cond_linebreak()+"\n");
        }
        return result.toString();
    }

    public static Set<Afs> extendYNMMap(final Map<FunctionSymbol, YNM[]> ynmmap) {
        // copy all YNM[] into one big one.
        int arity = 0;
        for (final FunctionSymbol f : ynmmap.keySet()) {
            final int ar = f.getArity();
            arity += ar;
        }
        final YNM[] allynm = new YNM[arity];
        arity = 0;
        for (final Map.Entry<FunctionSymbol, YNM[]> entry : ynmmap.entrySet()) {
            final FunctionSymbol f = entry.getKey();
            final YNM[] ynm = entry.getValue();
            System.arraycopy(ynm,0,allynm,arity,ynm.length);
            arity += f.getArity();
        }
        // now allynm contains the concatenation of all int[]s
        final Set<Afs> afss = new LinkedHashSet<Afs>();
        for (final boolean[] yn : new BasicPowerSet(allynm,allynm.length)) {
            final Afs afs = new Afs();
            arity = 0;
            for (final FunctionSymbol f : ynmmap.keySet()) {
                final int ar = f.getArity();
                final YNM[] args = new YNM[ar];
                for (int i = arity; i < arity+ar; i++) {
                    args[i-arity] = YNM.fromBool(yn[i]);
                }
                afs.setFiltering(f, args);
                arity += ar;
            }
            afss.add(afs);
        }
        return afss;
    }


    /**
     * Enumerates all afss, where for each f in fs a filtering should be determined
     * and a restriction on the maximal arity of the newly created filterings can be given.
     * It produces then dynamically via the iterator the new AFSs.
     * If collapsing is set to true, then also collapsing filterings will be generated
     * @param fs
     * @param collapsing
     * @return
     */
    public static Iterable<Afs> enumerateAfss(final Set<FunctionSymbol> fs, final boolean collapsing, final int restriction) {
        final Map<FunctionSymbol, YNM[]> fss = new LinkedHashMap<FunctionSymbol, YNM[]>(fs.size());
        for (final FunctionSymbol f : fs) {
            fss.put(f, null);
        }
        return Afs.extendAFS(new Afs(), fss, collapsing, restriction);
    }


    /**
     * Enumerates all afss, where for each f in fs a filtering should be determined (according to YNM patterns,
     * null patterns are allowed and are the same as everywhere Maybes)
     * and a restriction on the maximal arity of the newly created filterings.
     * It produces then dynamically via the iterator the new AFSs.
     * If collapsing is set to true, then also collapsing filterings will be generated
     * @param fs
     * @param collapsing
     * @return
     */
    public static Iterable<Afs> enumerateAfss(final Map<FunctionSymbol, YNM[]> fs, final boolean collapsing, final int restriction) {
        return Afs.extendAFS(new Afs(), fs, collapsing, restriction);
    }

    /**
     * takes an original afs, a set of
     * new function symbols where filterings should be integrated (according to YNM patterns,
     * null patterns are allowed and are the same as everywhere Maybes)
     * and a restriction on the maximal arity of the newly created filterings.
     * It produces then dynamically via the iterator the new AFSs.
     * If collapsing is set to true, then also collapsing filterings will be generated
     * @param original
     * @param fs
     * @param collapsing
     * @return
     */
    public static Iterable<Afs> extendAFS(final Afs original, final Map<FunctionSymbol, YNM[]> fs, final boolean collapsing, final int restriction) {
        Afs copy = null;
        final YNM[] emptyArr = new YNM[0];

        // first sort out all constants, they can trivially be added to the afs
        // and insert f's sorted by their arity (less inner loops)
        final SortedMap<FunctionSymbol,YNM[]> fss = new TreeMap<FunctionSymbol, YNM[]>(new Comparator<FunctionSymbol>() {
            @Override
            public int compare(final FunctionSymbol f, final FunctionSymbol g) {
                final int n = f.getArity() - g.getArity();
                if (n != 0) {
                    return n;
                } else {
                    return f.getName().compareTo(g.getName());
                }
            }});
        for (final Map.Entry<FunctionSymbol, YNM[]> fPat : fs.entrySet()) {
            final FunctionSymbol f = fPat.getKey();
            if (f.getArity() == 0) {
                if (copy == null) {
                    copy = new Afs(original);
                }
                copy.setFiltering(f, emptyArr);
            } else {
                fss.put(f, fPat.getValue());
            }
        }


        // okay, let us see, whether we have added some constant
        final Afs originalWithConstants = copy == null ? original : copy;

        // if we only had constants we return the one-element iterator
        final int n = fss.size();
        if (n == 0) {
            return new Iterable<Afs>() {
                @Override
                public Iterator<Afs> iterator() {
                    return new Iterator<Afs>() {
                        Afs next = originalWithConstants;
                        @Override
                        public boolean hasNext() {
                            return this.next != null;
                        }
                        @Override
                        public Afs next() {
                            final Afs res = this.next;
                            this.next = null;
                            return res;
                        }
                        @Override
                        public void remove() {
                            throw new UnsupportedOperationException();
                        }
                    };
                }
            };
        } else if (n == 1) {
            // or if we only have one remaining element then the set-construction  is not needed, too
            final Map.Entry<FunctionSymbol, YNM[]> fPat = fss.entrySet().iterator().next();
            return Afs.extendAFS(originalWithConstants, fPat.getKey(), fPat.getValue(), collapsing, restriction);
        }
        // otherwise we have to use the set iterator
        return Afs.extendAFSInternal(originalWithConstants, fss, collapsing, restriction);
    }

    /**
     * Same as extendAFS for sorted maps; moreover, it is required that fs is non-empty.
     */
    private static Iterable<Afs> extendAFSInternal(final Afs original, final SortedMap<FunctionSymbol,YNM[]> fs, final boolean collapsing, final int restriction) {
        /*
         * idea: first get one function symbol extensions of the original set => fIterable
         *       then for each of this afs's we use this method recursively on the
         *       remaining function symbols (remainingFs)
         */
        final Iterator<Map.Entry<FunctionSymbol, YNM[]>> fPatIt = fs.entrySet().iterator();
        final Map.Entry<FunctionSymbol, YNM[]> fPat = fPatIt.next();
        final FunctionSymbol f = fPat.getKey();
        final YNM[] pattern = fPat.getValue();
        final Iterable<Afs> fIterable = Afs.extendAFS(original, f, pattern, collapsing, restriction);
        if (fPatIt.hasNext()) {
            final FunctionSymbol g = fPatIt.next().getKey();
            final SortedMap<FunctionSymbol, YNM[]> remainingFs = fs.tailMap(g);
            final Iterator<Afs> fIterator = fIterable.iterator();
            return new Iterable<Afs>() {
                @Override
                public Iterator<Afs> iterator() {
                    return new Iterator<Afs>() {

                        boolean nextValid;
                        Afs nextResult = null;
                        Iterator<Afs> currentIt = null;

                        private void computeNext() {
                            while (!this.nextValid) {
                                if (this.currentIt == null) {
                                    if (fIterator.hasNext()) {
                                        final Afs currentFAfs = fIterator.next();
                                        this.currentIt = Afs.extendAFSInternal(currentFAfs, remainingFs, collapsing, restriction).iterator();
                                    } else {
                                        this.nextResult = null;
                                        this.nextValid = true;
                                    }
                                } else {
                                    if (this.currentIt.hasNext()) {
                                        this.nextResult = this.currentIt.next();
                                        this.nextValid = true;
                                    } else {
                                        this.currentIt = null;
                                    }
                                }
                            }
                        }

                        @Override
                        public boolean hasNext() {
                            if (!this.nextValid) {
                                this.computeNext();
                            }
                            return this.nextResult != null;
                        }

                        @Override
                        public Afs next() {
                            if (this.hasNext()) {
                                this.nextValid = false;
                                return this.nextResult;
                            } else {
                                throw new NoSuchElementException();
                            }
                        }

                        @Override
                        public void remove() {
                            throw new UnsupportedOperationException();
                        }
                    };
                }
            };
        } else {
            return fIterable;
        }
    }


    /**
     * takes an original afs, a new
     * function symbol not occurring in the afs up to now,
     * where filtering should be integrated (according to the YNM pattern,
     * a null pattern is allowed and is the same as [Maybe, ..., Maybe])
     * and a restriction on the maximal arity.
     * It produces then dynamically via the iterator the new AFSs,
     * where the filtering for f is fully determined, i.e. there is
     * no Maybe in the interpretation of f.
     * If collapsing is set to true, then also collapsing filterings will be generated.
     *
     * @param original
     * @param f
     * @param pattern
     * @param collapsing
     * @return
     */
    public static Iterable<Afs> extendAFS(final Afs original, final FunctionSymbol f, final YNM[] pattern, final boolean collapsing, final int restriction) {
        if (Globals.useAssertions) {
            assert (!original.filters.containsKey(f));
        }
        return new Iterable<Afs>() {
            private final boolean reverse = false;
            @Override
            public Iterator<Afs> iterator() {
                return new Iterator<Afs>() {
                    int coll;
                    boolean collapsePossible = collapsing;
                    Iterator<boolean[]> it = new BasicPowerSet(f.getArity(), restriction, pattern, reverse).iterator();
                    boolean nextValid = false;
                    boolean[] nextChoice = null;

                    private void computeNext() {
                        // if we have a collapsing filtering
                        // we can choose the non-collapsing filtering the next time
                        if (this.nextChoice != null && this.coll != -1) {
                            this.coll = -1;
                        } else {
                            // okay, we need a new pattern
                            if (this.it.hasNext()) {
                                this.nextChoice = this.it.next();
                                if (this.collapsePossible) {
                                    // check whether collapsing is possible
                                    int nr = 0; // count nr of used args
                                    final int n = this.nextChoice.length;
                                    this.coll = -1;
                                    for (int pos = 0; pos < n; pos++) {
                                        if (this.nextChoice[pos]) {
                                            nr++;
                                            if (nr == 2) {
                                                // as the patterns will be generated in increasing order,
                                                // we will from this point onwards only see patterns with
                                                // at least two arguments => no collapsing possible any more
                                                this.collapsePossible = false;
                                                this.coll = -1;
                                                break;
                                            }
                                            this.coll = pos;
                                        }
                                    }
                                } else {
                                    this.coll = -1;
                                }
                            } else {
                                this.nextChoice = null;
                            }
                        }
                        this.nextValid = true;
                    }

                    @Override
                    public boolean hasNext() {
                        if (!this.nextValid) {
                            this.computeNext();
                        }
                        return this.nextChoice != null;
                    }

                    @Override
                    public Afs next() {
                        if (this.hasNext()) {
                            this.nextValid = false;
                            final Afs res = new Afs(original);
                            if (this.coll != -1) {
                                res.setCollapsing(f, this.coll);
                            } else {
                                res.setFiltering(f, this.nextChoice);
                            }
                            return res;
                        } else {
                            throw new NoSuchElementException();
                        }
                    }

                    @Override
                    public void remove() {
                        throw new UnsupportedOperationException();
                    }

                };
            }
        };
    }

    public static Set<Afs> extendWithCollapsing(final Afs original, final List<FunctionSymbol> fs) {
        return Afs.extendWithCollapsing(original, new Afs(), fs, 0);
    }

    private static Set<Afs> extendWithCollapsing(final Afs original, final Afs upToNow, final List<FunctionSymbol> fs, final int nextFunc) {
        final Set<Afs> afss = new LinkedHashSet<Afs>();
        if (nextFunc < fs.size()) {
            final FunctionSymbol f = fs.get(nextFunc);
            final Filtering filtering = original.filters.get(f);
            if (Afs.countYES(filtering.x) != 1) {
                upToNow.filters.put(f, filtering);
                return Afs.extendWithCollapsing(original, upToNow, fs, nextFunc+1);
            }
            final Afs newUpToNow = new Afs();
            newUpToNow.filters = new LinkedHashMap<FunctionSymbol,Filtering>(upToNow.filters);
            upToNow.filters.put(f, filtering);
            newUpToNow.filters.put(f, new Filtering(filtering.x, true));
            afss.addAll(Afs.extendWithCollapsing(original, newUpToNow, fs, nextFunc+1));
            afss.addAll(Afs.extendWithCollapsing(original, upToNow, fs, nextFunc+1));
        } else {
//          System.out.println("Adding "+upToNow);
            afss.add(upToNow);
        }
        return afss;
    }

    public void setFiltering(final FunctionSymbol f, final int i, final YNM val) {
        Filtering filtering = this.filters.get(f);
        if (filtering == null) {
            this.setNoFiltering(f);
            filtering = this.filters.get(f);
        }
        filtering.x[i] = val;
    }

    public String toCodish(final FreshNameGenerator vars, final FreshNameGenerator funcs) {
        final StringBuffer res = new StringBuffer("[");
        boolean first = true;
        for (final Map.Entry<FunctionSymbol,Filtering> entry : this.filters.entrySet()) {
            final FunctionSymbol f = entry.getKey();
            final Filtering filtering = entry.getValue();
            if (!filtering.y) {
                if (first) {
                    first = false;
                } else {
                    res.append(", ");
                }
                res.append("flag(");
                res.append(funcs.getFreshName(f.getName(), true));
                res.append(")");
            }
        }
        for (final Map.Entry<FunctionSymbol,Filtering> entry : this.filters.entrySet()) {
            final FunctionSymbol f = entry.getKey();
            final Filtering filtering = entry.getValue();
            for (int i = 0; i < filtering.x.length; i++) {
                if (filtering.x[i] == YNM.YES) {
                    if (first) {
                        first = false;
                    } else {
                        res.append(", ");
                    }
                    res.append(funcs.getFreshName(f.getName(), true));
                    res.append("/");
                    res.append(i+1);
                }
            }
        }
        res.append("]");
        return res.toString();
    }

    private FunctionSymbol getFilteredSymbol(final FunctionSymbol f, final int newArity) {
        if (this.symbolMap == null) {
            this.symbolMap = new BidirectionalMap<FunctionSymbol, FunctionSymbol>();
        }
        FunctionSymbol filteredF = this.symbolMap.getLR(f);
        if (filteredF == null || filteredF.getArity() != newArity) {
            // new symbol needed
            String newName = f.getName();
            filteredF = FunctionSymbol.create(newName, newArity);
            while (this.symbolMap.containsValueLR(filteredF)) {
                newName = newName + "'";
                filteredF = FunctionSymbol.create(newName, newArity);
            }
            this.symbolMap.putLR(f, filteredF);
        }
        return filteredF;
    }

    public FunctionSymbol filter(final FunctionSymbol f) {
        final Filtering filtering = this.filters.get(f);
        if (filtering == null) {
            return this.getFilteredSymbol(f, f.getArity());
        }
        if (filtering.y) {
            return null;
        }
        final int newArity = Afs.countYES(filtering.x);
        return this.getFilteredSymbol(f, newArity);
    }

    public Map<FunctionSymbol, FunctionSymbol> getSymbolMap(final Collection<FunctionSymbol> sig) {
        final Map<FunctionSymbol, FunctionSymbol> symbolMap = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        for (final FunctionSymbol f : sig) {
            final FunctionSymbol filteredF = this.filter(f);
            if (filteredF != null) {
                symbolMap.put(f, filteredF);
            }
        }
        return symbolMap;
    }

    /**
     * Checks whether this afs has collapsing arguments
     */
    public boolean hasCollapsingArgs() {
        for (final Map.Entry<FunctionSymbol, Filtering> filter : this.filters.entrySet()) {
            final FunctionSymbol symbol = filter.getKey();
            final Pair<YNM[], Boolean> filtering = this.getFiltering(symbol);
            if(filtering.y) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether this afs really filters some arguments or function symbols
     */
    public boolean isFiltering() {
       for (final Map.Entry<FunctionSymbol,Filtering> entry : this.filters.entrySet()) {
           final Filtering f = entry.getValue();
           if (f.y) {
            return true;
        }
           for (final YNM x : f.x) {
               if (x != YNM.YES) {
                return true;
            }
           }
       }
       return false;
    }

    public static Integer getOriginalPos(int position, final YNM[] filterList) {
        for (int i = 0; i< filterList.length; i++) {
            if (filterList[i] == YNM.YES) {
                if (i == position) {
                    return position;
                }
            } else {
                position++;
            }
        }
        return null;
    }


    public String toNguyen() {
        final StringBuffer res = new StringBuffer();
        for (final Map.Entry<FunctionSymbol,Filtering> entry : this.filters.entrySet()) {
            final FunctionSymbol f = entry.getKey();
            final int arity = f.getArity();
            final Filtering filtering = entry.getValue();
            res.append(f.getName());
            res.append("/");
            res.append(arity);
            res.append("-[");
            boolean first = true;
            for (int i = 0; i < filtering.x.length; i++) {
                if (filtering.x[i] == YNM.YES) {
                    if (first) {
                        first = false;
                    } else {
                        res.append(",");
                    }
                    res.append(i+1);
                }
            }
            res.append("].\n");
        }
        return res.toString();
    }

    public boolean hasFilter(final FunctionSymbol f) {
        return this.filters.containsKey(f);
    }

    public boolean sameFilteringAs(final Afs pi) {
        final Set<FunctionSymbol> cap = new LinkedHashSet<FunctionSymbol>(this.filters.keySet());
        cap.retainAll(pi.filters.keySet());
        /* for each defined function symbol f, this(f) = pi(f) must hold */
        Pair<YNM[], Boolean> filteringThis, filteringOther;
        for(final FunctionSymbol f : cap) {
            filteringThis = this.getFiltering(f);
            filteringOther = pi.getFiltering(f);
            if( filteringThis.y != filteringOther.y ||
                filteringThis.x.length != filteringOther.x.length ) {
                return false;
            }
            for(int i = 0; i < filteringThis.x.length; ++i) {
                if( filteringThis.x[i] != filteringOther.x[i] ) {
                    return false;
                }
            }
        }
        /* every other function symbol must not be filtered away */
        for(final Map.Entry<FunctionSymbol, Filtering> entry : this.filters.entrySet()) {
            if( !cap.contains(entry.getKey()) ) {
                if( entry.getValue().y ) {
                    return false;
                }
                for (final YNM element : entry.getValue().x) {
                    if(element != YNM.YES) {
                        return false;
                    }
                }
            }
        }
        for(final Map.Entry<FunctionSymbol, Filtering> entry : pi.filters.entrySet()) {
            if( !cap.contains(entry.getKey()) ) {
                if( entry.getValue().y ) {
                    return false;
                }
                for (final YNM element : entry.getValue().x) {
                    if(element != YNM.YES) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /**
     * creates an AFS-entry for the fiven input.
     * Both the filter an the permuation may be null
     * (e.g. filter = null for pure LPOS, or perm = null for AFS + MPO)
     * @param f
     * @param filter
     * @param doc
     * @param xmlMetaData
     * @param perm
     * @return
     */
    public  Element toCPFEntry(final FunctionSymbol f, Pair<YNM[], Boolean> filter, final Document doc, final XMLMetaData xmlMetaData, final Permutation perm) {
        if (filter == null) {
            filter = Afs.getNoFiltering(f.getArity());
        }
        final YNM[] args = filter.x;
        final boolean isCollapsing = filter.y;
        Element filt;
        if (isCollapsing) {
            int pos;
            for (pos = 0; args[pos]!=YNM.YES; pos++) {
                ;
            }
            filt = CPFTag.COLLAPSING.create(doc, (pos + 1));
        } else {
            filt = CPFTag.NON_COLLAPSING.create(doc);
            if (perm == null) {
                for (int pos = 0; pos < args.length; pos++) {
                    if (args[pos] == YNM.YES) {
                        filt.appendChild(CPFTag.POSITION.create(doc, (pos + 1)));
                    }
                }
            } else {
                for (int i = 0; i < perm.size(); i++) {
                    // for CPF we need the original position of the args
                    final int j = Afs.getOriginalPos(perm.get(i), args);
                    if (args[j] == YNM.YES) {
                        filt.appendChild(CPFTag.POSITION.create(doc, j + 1));
                    }
                }
            }
        }

        return CPFTag.ARGUMENT_FILTER_ENTRY.create(doc,
                f.toCPF(doc, xmlMetaData),
                CPFTag.ARITY.create(doc, f.getArity()),
                filt
                );

    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element entries = CPFTag.ARGUMENT_FILTER.create(doc);
        for (final Map.Entry<FunctionSymbol,Filtering> f : this.filters.entrySet()) {
            entries.appendChild(this.toCPFEntry(f.getKey(), f.getValue(), doc, xmlMetaData, null));
        }
        return entries;
    }
}
