package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Relation generic between variables states (generic).
 * @author marinag, cryingshadow
 */
public class GenericRelation<T, V extends INextValue<T>> implements Iterable<Pair<String, V>>, Cloneable, Exportable {

    /**
     * Pairs each variable with its next state (underlying) value
     */
    ImmutableList<Pair<String, T>> transitions;

    /**
     * Maps each variable with its next state (underlying) value
     */
    ImmutableMap<String, T> transMap;

    /**
     * Pairs each variable with its next state value
     */
    ImmutableList<Pair<String, V>> transVec;

    /**
     * Creates a relation according to the given transitions list
     */
    protected GenericRelation(final List<Pair<String, V>> transVec) {
        this.transVec = ImmutableCreator.create(transVec);
        final List<Pair<String, T>> trans = new ArrayList<>();
        final Map<String,T> tMap = new HashMap<>();
        for (final Pair<String, V> entry : this.transVec) {
            final T value = entry.y == null ? null : entry.y.getValue();
            trans.add(new Pair<>(entry.x, value));
            tMap.put(entry.x, value);
        }
        this.transitions = ImmutableCreator.create(trans);
        this.transMap = ImmutableCreator.create(tMap);
    }

    /**
     * @param v term
     * @return the given term under this relation
     */
    public T apply(final V v) {
        if (v == null || v.getValue() == null) {
            return null;
        }
        final Set<String> ndtVars = new HashSet<>();
        for (final Pair<String, V> entry : this.transVec) {
            if (entry.y == null || entry.y.getValue() == null) {
                ndtVars.add(entry.x);
            }
        }
        ndtVars.retainAll(v.getVariables());
        if (!ndtVars.isEmpty()) {
            return null;
        }
        return v.apply(this.getTransitions());
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj == null || !(obj instanceof GenericRelation)) {
            return false;
        }
        final GenericRelation relation = (GenericRelation) obj;
        return this.transVec.equals(relation.transVec);
    }

    @Override
    public String export(Export_Util eu) {
        return eu.set(this.transitions, Export_Util.RULES);
    }

    public T get(final String name) {
        return this.transMap.get(name);
    }

    public Set<String> getNondet() {
        final Set<String> ndtVars = this.getReferedVariableNames();
        ndtVars.removeAll(this.getVariablesNames());
        return ndtVars;
    }

    public Set<String> getReferedVariableNames() {
        final Set<String> vars = new HashSet<>();
        for (final Pair<String, V> pair : this.getTransVector()) {
            if (pair.y == null) {
                continue;
            }
            vars.addAll(pair.y.getVariables());
        }
        return vars;
    }

    public ImmutableList<Pair<String, T>> getTransitions() {
        return this.transitions;
    }

    public ImmutableList<Pair<String, V>> getTransVector() {
        return this.transVec;
    }

    public List<Pair<String, V>> getTrimTrans() {
        final List<Pair<String, V>> newT = new ArrayList<>();
        for (final Pair<String, V> entry : this.getTransVector()) {
            if (!entry.getValue().isIdentity(entry.x)) {
                newT.add(entry);
            }
        }
        return newT;
    }

    public Set<String> getVariablesNames() {
        final Set<String> vars = new HashSet<>();
        for (final Pair<String, V> item : this.transVec) {
            vars.add(item.getKey());
        }
        return vars;
    }

    @Override
    public int hashCode() {
        return this.transVec.hashCode();
    }

    /**
     * @return true if this is an identity relation, false otherwise
     */
    public boolean isIdentity() {
        for (final Pair<String, V> pair : this.transVec) {
            if (!this.isIdentity(pair)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public Iterator<Pair<String, V>> iterator() {
        return this.transVec.iterator();
    }

    @Override
    public String toString() {
        return this.transitions.toString();
    }

    protected boolean isIdentity(final Pair<String, V  > pair) {
        final INextValue<T> val = pair.y;
        if (val == null) {
            return false;
        }
        return val.isIdentity(pair.x);
    }

}
