package aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class RuleSet<T extends GeneralizedRule> extends AbstractSet<T> {

    private final Map<FunctionSymbol, Set<T>> rules = new LinkedHashMap<FunctionSymbol, Set<T>>();

    private int size;

    public RuleSet() {
        this(Collections.<T>emptySet());
    }

    public RuleSet(final RuleSet<T> c) {
        for (final Map.Entry<FunctionSymbol, Set<T>> e : c.rules.entrySet()) {
            this.rules.put(e.getKey(), new LinkedHashSet<T>(e.getValue()));
            this.size += e.getValue().size();
        }
    }

    public RuleSet(final Collection<? extends T> c) {
        for (final T rule : c) {
            this.addIntern(rule);
        }
    }

    @Override
    public boolean add(final T e) {
        return this.addIntern(e);
    }

    /**
     * This is split from add to support {@link ImmutableRuleSet}
     */
    private boolean addIntern(final T e) {
        Set<T> set = this.rules.get(e.getRootSymbol());
        if (set == null) {
            set = new LinkedHashSet<T>();
            this.rules.put(e.getRootSymbol(), set);
        }
        final boolean rv = set.add(e);
        if (rv) {
            this.size++;
        }
        return rv;
    }

    @Override
    public void clear() {
        this.rules.clear();
        this.size = 0;
    }

    @Override
    public boolean remove(final Object o) {
        if (!(o instanceof GeneralizedRule)) {
            return false;
        }
        final GeneralizedRule r = (GeneralizedRule) o;
        final Set<T> set = this.rules.get(r.getRootSymbol());
        final boolean rv = (set != null && set.remove(r));
        if (rv) {
            this.size--;
            if (set.isEmpty()) {
                this.rules.remove(r.getRootSymbol());
            }
        }
        return rv;
    }

    @Override
    public boolean contains(final Object o) {
        if (!(o instanceof GeneralizedRule)) {
            return false;
        }
        final GeneralizedRule r = (GeneralizedRule) o;
        final Set<T> set = this.rules.get(r.getRootSymbol());
        return set != null && set.contains(o);
    }

    @Override
    public Iterator<T> iterator() {
        return IterableConcatenator.create(this.rules.values()).iterator();
    }

    @Override
    public int size() {
        return this.size;
    }

    public Set<T> getSubsetByRootSymbol(final FunctionSymbol rootSymbol) {
        final Set<T> set = this.rules.get(rootSymbol);
        if (set == null) {
            return Collections.emptySet();
        } else {
            return ImmutableCreator.create(set);
        }
    }

    public ImmutableSet<FunctionSymbol> getDefinedSymbols() {
        return ImmutableCreator.create(this.rules.keySet());
    }

    /**
     * More efficient variant of Term.isNormal
     */
    public boolean termIsNormal(final TRSTerm t) {
        if (t.isVariable()) {
            return true;
        }

        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
        for (final T rule : this.getSubsetByRootSymbol(fa.getRootSymbol())) {
            if (rule.getLeft().matches(t)) {
                return false;
            }
        }
        for (final TRSTerm arg : fa.getArguments()) {
            if (!this.termIsNormal(arg)) {
                return false;
            }
        }

        return true;
    }

}
