package aprove.verification.dpframework.CSDPProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class ReplacementMap
        implements Immutable, Exportable {

    private final ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> map;

    private static final long serialVersionUID = 2708239126516008086L;

    private ReplacementMap(
            Map<FunctionSymbol, ImmutableSet<Integer>> replacementMap) {
        this.map = ImmutableCreator.create(replacementMap);
    }

    public static ReplacementMap create(
            Map<FunctionSymbol, ImmutableSet<Integer>> replacementMap) {
        return new ReplacementMap(replacementMap);
    }

    public static ReplacementMap create(ReplacementMap rm,
            Set<FunctionSymbol> usedSymbols) {
        ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> map = rm.getMap();
        Map<FunctionSymbol, ImmutableSet<Integer>> newMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<Integer>>();
        for (FunctionSymbol f : usedSymbols) {
            ImmutableSet<Integer> active = map.get(f);
            if (Globals.useAssertions) {
                assert (active != null);
            }

            newMap.put(f, active);
        }

        return new ReplacementMap(ImmutableCreator.create(newMap));
    }

    private void getNonReplacingSubterms(TRSTerm t, Set<TRSTerm> subterms,
            boolean nonreplacing) {
        if (t.isVariable()) {
            return;
        }

        TRSFunctionApplication s = (TRSFunctionApplication) t;
        FunctionSymbol sym = s.getRootSymbol();

        int arity = sym.getArity();
        ImmutableSet<Integer> m = this.map.get(sym);

        for (Integer i = 0; i < arity; ++i) {
            if (nonreplacing || !m.contains(i)) {
                subterms.add(s.getArgument(i));
                this.getNonReplacingSubterms(s.getArgument(i), subterms, true);
            } else {
                this.getNonReplacingSubterms(s.getArgument(i), subterms, false);
            }
        }
    }

    public Set<TRSTerm> getNonReplacingSubterms(TRSTerm t) {
        Set<TRSTerm> subs = new LinkedHashSet<TRSTerm>();
        this.getNonReplacingSubterms(t, subs, false);
        return subs;
    }

    private void getReplacingSubterms(TRSTerm t, Set<TRSTerm> subterms) {
        subterms.add(t);

        if (t.isVariable()) {
            return;
        }

        TRSFunctionApplication s = (TRSFunctionApplication) t;
        FunctionSymbol sym = s.getRootSymbol();

        for (Integer i : this.map.get(sym)) {
            this.getReplacingSubterms(s.getArgument(i), subterms);
        }
    }

    public Set<TRSTerm> getReplacingSubterms(TRSTerm t) {
        Set<TRSTerm> subs = new LinkedHashSet<TRSTerm>();
        this.getReplacingSubterms(t, subs);
        return subs;
    }

    private void getReplacingVariables(TRSTerm t, Set<TRSVariable> vars) {

        if (t.isVariable()) {
            vars.add((TRSVariable) t);
            return;
        }

        TRSFunctionApplication s = (TRSFunctionApplication) t;
        FunctionSymbol sym = s.getRootSymbol();

        for (Integer i : this.map.get(sym)) {
            this.getReplacingVariables(s.getArgument(i), vars);
        }
    }

    public Set<TRSVariable> getReplacingVariables(TRSTerm t) {
        Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        this.getReplacingVariables(t, vars);
        return vars;
    }

    public Set<TRSVariable> getNonReplacingVariables(TRSTerm t) {
        Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        this.getNonReplacingVariables(t, vars);
        return vars;
    }

    private void getNonReplacingVariables(TRSTerm t, Set<TRSVariable> vars) {
        if (t.isVariable()) {
            return;
        }

        TRSFunctionApplication u = (TRSFunctionApplication) t;

        FunctionSymbol f = u.getRootSymbol();

        Set<Integer> map = this.getMap().get(f);
        Integer arity = f.getArity();

        for (Integer i = 0; i < arity; ++i) {
            if (map.contains(i)) {
                this.getNonReplacingVariables(u.getArgument(i), vars);
            }
            vars.addAll(u.getVariables());
        }
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder s = new StringBuilder();

        Map<ImmutableSet<Integer>, Set<FunctionSymbol>> revMap = new LinkedHashMap<ImmutableSet<Integer>, Set<FunctionSymbol>>();
        Set<FunctionSymbol> unrestricted = new LinkedHashSet<FunctionSymbol>();
        Set<FunctionSymbol> completelyRestricted = new LinkedHashSet<FunctionSymbol>();

        for (Map.Entry<FunctionSymbol, ImmutableSet<Integer>> repMapEntry : this.map
                .entrySet()) {
            FunctionSymbol sym = repMapEntry.getKey();
            if (sym.getArity() == 0) {
                continue;
            }
            ImmutableSet<Integer> set = repMapEntry.getValue();
            if (set.size() == 0) {
                completelyRestricted.add(sym);
                continue;
            }
            if (set.size() == sym.getArity()) {
                unrestricted.add(sym);
                continue;
            }
            Set<FunctionSymbol> syms = revMap.get(set);
            if (syms == null) {
                syms = new LinkedHashSet<FunctionSymbol>();
                revMap.put(set, syms);
            }
            syms.add(sym);
        }

        if (!unrestricted.isEmpty()) {
            s.append(o.export("The symbols in ")
                    + o.set(unrestricted, Export_Util.SIMPLESET)
                    + o.export(" are replacing on all positions.")
                    + o.cond_linebreak());
        }

        for (Map.Entry<ImmutableSet<Integer>, Set<FunctionSymbol>> entry : revMap
                .entrySet()) {
            Set<FunctionSymbol> syms = entry.getValue();
            ArrayList<Integer> shiftSet = new ArrayList<Integer>(entry.getKey()
                    .size());
            for (Integer i : entry.getKey()) {
                shiftSet.add(i + 1);
            }
            s.append(o.export("For all symbols ") + o.math("f")
                    + o.export(" in ") + o.set(syms, Export_Util.SIMPLESET)
                    + o.export(" we have ") + o.math(o.mu() + "(f) = ")
                    + o.set(shiftSet, Export_Util.SIMPLESET) + o.export(".")
                    + o.cond_linebreak());
        }

        if (!completelyRestricted.isEmpty()) {
            s.append(o.export("The symbols in ")
                    + o.set(completelyRestricted, Export_Util.SIMPLESET)
                    + o.export(" are not replacing on any position.")
                    + o.cond_linebreak());
        }

        return s.toString();
    }

    public final ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> getMap() {
        return this.map;
    }

    /**
     * Checks if t is in Q-mu-normal form. ([E08], Definition ??)
     *
     * @param q
     *            the set of terms Q
     * @param t
     *            the term to check
     * @return true, if t is in Q-mu-normal form.
     */
    public final boolean inQMuNormalForm(QTermSet q, TRSTerm t) {
        if (t.isVariable()) {
            return true;
        }

        TRSFunctionApplication term = (TRSFunctionApplication) t;
        if (q.canBeRewrittenAtRoot(term)) {
            return false;
        }

        for (Integer i : this.map.get(term.getRootSymbol())) {
            if (!this.inQMuNormalForm(q, term.getArgument(i))) {
                return false;
            }
        }

        return true;
    }

    /**
     * Computes the set of hidden symbols of a set of rules.
     */
    public final ImmutableSet<FunctionSymbol> computeHiddenSymbols(Set<Rule> r) {
        Set<FunctionSymbol> syms = new LinkedHashSet<FunctionSymbol>();

        for (Rule rule : r) {
            TRSTerm rhs = rule.getRight();
            /* well, could not call this optimized with a straight face */
            for (TRSTerm t : this.getNonReplacingSubterms(rhs)) {
                if (!t.isVariable()) {
                    TRSFunctionApplication f = (TRSFunctionApplication) t;
                    syms.add(f.getRootSymbol());
                }
            }
        }

        return ImmutableCreator.create(syms);
    }

    /**
     * returns true if no function symbol is restricted in any position.
     */
    public boolean isUnrestricted() {
        for (Map.Entry<FunctionSymbol, ImmutableSet<Integer>> repMapEntry : this.map
                .entrySet()) {
            FunctionSymbol f = repMapEntry.getKey();
            ImmutableSet<Integer> active = repMapEntry.getValue();
            int arity = f.getArity();
            if (arity > 0) {
                for (Integer i = 0; i < arity; ++i) {
                    if (!active.contains(i)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /**
     * Check that the rule is conservative. I.e. that Var^\mu(t) \subseteq
     * Var^\mu(s).
     *
     * @param s_to_t
     * @return
     */
    public boolean isConservative(Rule s_to_t) {
        Set<TRSVariable> sVars = this.getReplacingVariables(s_to_t.getLeft());
        Set<TRSVariable> tVars = this.getReplacingVariables(s_to_t.getRight());
        return sVars.containsAll(tVars);
    }

    public boolean isConservative(Iterable<Rule> rules) {
        for (Rule rule : rules) {
            if (!this.isConservative(rule)) {
                return false;
            }
        }
        return true;
    }

    public boolean isStronglyConservative(Rule s_to_t) {
        TRSTerm s = s_to_t.getLeft();
        TRSTerm t = s_to_t.getRight();

        Set<TRSVariable> sMuVars = this.getReplacingVariables(s);
        Set<TRSVariable> tMuVars = this.getReplacingVariables(t);

        Set<TRSVariable> sNonMuVars = this.getNonReplacingVariables(s);
        Set<TRSVariable> tNonMuVars = this.getNonReplacingVariables(t);

        // first check normal conservativeness
        if (!sMuVars.containsAll(tMuVars)) {
            return false;
        }

        // check VarMu(s) \cup \VarNonMu(s) = \emptyset
        // warning: sMuVars is modified
        sMuVars.retainAll(sNonMuVars);
        if (!sMuVars.isEmpty()) {
            return false;
        }

        // check VarMu(t) \cup \VarNonMu(t) = \emptyset
        // warning: tMuVars is modified
        tMuVars.retainAll(tNonMuVars);
        if (!tMuVars.isEmpty()) {
            return false;
        }

        return true;
    }

    public boolean isStronglyConservative(Iterable<Rule> rules) {
        for (Rule rule : rules) {
            if (!this.isStronglyConservative(rule)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * Returns <code>true</code> iff arg \in \mu(f).
     * @param f
     * @param arg
     * @return
     */
    public boolean isReplacing(FunctionSymbol f, int arg) {
        ImmutableSet<Integer> rm = this.map.get(f);
        return rm.contains(arg);
    }

    /**
     * Returns <code>true</code> iff position <code>p</code> in term
     * <code>t</code> is replacing.
     * @param t
     * @param p
     * @return
     */
    public boolean isReplacing(TRSTerm t, Position p) {
        return this.isReplacing(t, p.iterator());
    }

    private boolean isReplacing(TRSTerm t, Iterator<Integer> p) {
        if (!p.hasNext()) {
            return true;
        }

        if (Globals.useAssertions) {
            assert (!t.isVariable());
        }

        TRSFunctionApplication t2 = (TRSFunctionApplication) t;
        FunctionSymbol f = t2.getRootSymbol();
        int arg = p.next();
        if (!this.isReplacing(f, arg)) {
            return false;
        }

        return this.isReplacing(t2.getArguments().get(arg), p);
    }

    /** Check that hole in C is at replacing position. */
    public boolean isReplacingContext(final Context c) {
        if (c.isEmptyContext()) {
            return true;
        }
        NonEmptyContext nec = (NonEmptyContext) c;
        FunctionSymbol f = nec.getRootSymbol();
        int arg = nec.getPositionOfDirectSubcontext();

        if (!this.isReplacing(f, arg)) {
            return false;
        }

        return this.isReplacingContext(nec.getDirectSubcontext());
    }
}
