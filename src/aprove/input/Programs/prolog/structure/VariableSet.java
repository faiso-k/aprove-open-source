/**
 *
 */
package aprove.input.Programs.prolog.structure;

import java.util.*;

/**
 * @author cryingshadow
 *
 */
public class VariableSet extends LinkedHashSet<PrologVariable> {

    /**
     * Automatically generated.
     */
    private static final long serialVersionUID = -292217218606261525L;

    /**
     * Standard constructor for empty set.
     */
    public VariableSet() {
        super();
    }

    /**
     * Constructs a set containing the elements in the specified collection.
     * @param c The collection.
     */
    public VariableSet(final Collection<? extends PrologVariable> c) {
        super(c);
    }

    /**
     * Returns a new VariableSet with the same elements (same objects).
     * @return A new VariableSet with the same elements (same objects).
     */
    public VariableSet copy() {
        return new VariableSet(this);
    }

    /**
     * Checks whether the specified set is disjoint from the current one.
     * @param set The set to check.
     * @return True if the specified set is disjoint from the current one.
     */
    public boolean disjoint(final Set<? extends PrologVariable> set) {
        final VariableSet check = this.copy();
        check.retainAll(set);
        return check.isEmpty();
    }

    /**
     * Returns a new VariableSet containing all and only abstract variables in the current set.
     * @return A new VariableSet containing all and only abstract variables in the current set.
     */
    public VariableSet restrictToAbstractVariables() {
        final VariableSet res = new VariableSet(this);
        final VariableSet toDel = new VariableSet();
        for (final PrologVariable v : res) {
            if (!v.isAbstractVariable()) {
                toDel.add(v);
            }
        }
        res.removeAll(toDel);
        return res;
    }

    /**
     * Returns a new VariableSet containing all and only non-abstract variables in the current set.
     * @return A new VariableSet containing all and only non-abstract variables in the current set.
     */
    public VariableSet restrictToNonAbstractVariables() {
        final VariableSet res = new VariableSet(this);
        final VariableSet toDel = new VariableSet();
        for (final PrologVariable v : res) {
            if (!v.isNonAbstractVariable()) {
                toDel.add(v);
            }
        }
        res.removeAll(toDel);
        return res;
    }

}
