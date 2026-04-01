package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;

/**
 * Represent a mutable set (conjunction) of integer relations between variables. This set must not contain null.
 * @author Janine Repke, Peter Schneider-Kamp, cryingshadow
 */
public class IntegerRelationSet implements Set<IntegerRelation>, Substitutable, SMTSExpressible<SBool> {

    /**
     * ID for equations.
     */
    private final static int EQUATIONS = 1;

    /**
     * ID for undirected inequations.
     */
    private final static int INEQUATIONS = 2;

    /**
     * ID for strict directed inequations.
     */
    private final static int STRICT_INEQUATIONS = 3;

    /**
     * ID for weak directed inequations.
     */
    private final static int WEAK_INEQUATIONS = 4;

    /**
     * Equations lhs = rhs.
     */
    private final Set<IntegerRelation> equations;

    /**
     * Inequalities lhs != rhs.
     */
    private final Set<IntegerRelation> inequalities;

    /**
     * Inequalities lhs < rhs.
     */
    private final Set<IntegerRelation> strictinequalities;

    /**
     * Inequalities lhs <= rhs.
     */
    private final Set<IntegerRelation> weakinequalities;

    /**
     * Creates an empty set.
     */
    public IntegerRelationSet() {
        this.equations = new LinkedHashSet<IntegerRelation>();
        this.inequalities = new LinkedHashSet<IntegerRelation>();
        this.strictinequalities = new LinkedHashSet<IntegerRelation>();
        this.weakinequalities = new LinkedHashSet<IntegerRelation>();
    }

    /**
     * Creates a set containing all elements in the specified set.
     * @param set The set containing the elements (must not contain null).
     */
    public IntegerRelationSet(Set<? extends IntegerRelation> set) {
        this();
        this.addAll(set);
    }

    /**
     * @param eqs The equations.
     * @param ineqs The undirected inequalities.
     * @param strict The strict directed inequalities.
     * @param weak The weak directed inequalities.
     */
    public IntegerRelationSet(
        Set<IntegerRelation> eqs,
        Set<IntegerRelation> ineqs,
        Set<IntegerRelation> strict,
        Set<IntegerRelation> weak
    ) {
        this.equations = eqs;
        this.inequalities = ineqs;
        this.strictinequalities = strict;
        this.weakinequalities = weak;
    }

    @Override
    public boolean add(IntegerRelation rel) {
        // adding null will yield a NullPointerException
        switch (rel.getRelationType()) {
            case EQ:
                return this.equations.add(rel);
            case NE:
                return this.inequalities.add(rel);
            case LT:
            case GT:
                return this.strictinequalities.add(rel);
            case LE:
            case GE:
                return this.weakinequalities.add(rel);
            default:
                throw new IllegalStateException("Someone found a new way to build relations!");
        }
    }

    @Override
    public boolean addAll(Collection<? extends IntegerRelation> c) {
        boolean res = false;
        for (IntegerRelation rel : c) {
            res |= this.add(rel);
        }
        return res;
    }

    @Override
    public IntegerRelationSet applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this.applySubstitution(Substitution.toSubstitution(sigma));
    }

    @Override
    public IntegerRelationSet applySubstitution(Substitution sigma) {
        Set<IntegerRelation> old = new LinkedHashSet<IntegerRelation>(this);
        this.clear();
        for (IntegerRelation rel : old) {
            this.add(rel.applySubstitution(sigma));
        }
        return this;
    }

    @Override
    public void clear() {
        this.equations.clear();
        this.inequalities.clear();
        this.strictinequalities.clear();
        this.weakinequalities.clear();
    }

    /**
     * Removes all equations from this set.
     */
    public void clearEquations() {
        this.equations.clear();
    }

    /**
     * Removes all weak directed inequalities from this set.
     */
    public void clearWeakDirectedInequalities() {
        this.weakinequalities.clear();
    }

    @Override
    public boolean contains(Object o) {
        if (o instanceof IntegerRelation) {
            IntegerRelation rel = (IntegerRelation)o;
            switch (rel.getRelationType()) {
                case NE:
                    return this.inequalities.contains(rel);
                case EQ:
                    return this.equations.contains(rel);
                case LE:
                case GE:
                    return this.weakinequalities.contains(rel);
                case LT:
                case GT:
                    return this.strictinequalities.contains(rel);
                default:
                    throw new IllegalStateException("Someone found a new way build relations!");
            }
        }
        return false;
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        for (Object o : c) {
            if (!this.contains(o)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || !(o instanceof Set<?>)) {
            return false;
        }
        Set<?> other = (Set<?>)o;
        return this.containsAll(other) && other.containsAll(this);
    }

    /**
     * @return A set containing all directed (weak and strict) inequalities in this set.
     */
    public Set<IntegerRelation> getDirectedInequalities() {
        Set<IntegerRelation> res = new LinkedHashSet<IntegerRelation>();
        res.addAll(this.strictinequalities);
        res.addAll(this.weakinequalities);
        return res;
    }

    /**
     * @return The equations in this set.
     */
    public Set<IntegerRelation> getEquations() {
        return new LinkedHashSet<IntegerRelation>(this.equations);
    }

    /**
     * @return This set without undirected inequalities.
     */
    public IntegerRelationSet getRelationsWithoutUndirectedInequalities() {
        return
            new IntegerRelationSet(
                this.equations,
                Collections.<IntegerRelation>emptySet(),
                this.strictinequalities,
                this.weakinequalities
            );
    }

    /**
     * @return The strict directed inequalities (lhs < rhs or lhs > rhs) in this relation set.
     */
    public Set<IntegerRelation> getStrictDirectedInequalities() {
        return new LinkedHashSet<IntegerRelation>(this.strictinequalities);
    }

    /**
     * @return The undirected inequalities (lhs != rhs) in this relation set.
     */
    public Set<IntegerRelation> getUndirectedInequalities() {
        return new LinkedHashSet<IntegerRelation>(this.inequalities);
    }

    /**
     * @return The weak directed inequalities (lhs <= rhs or lhs >= rhs) in this relation set.
     */
    public Set<IntegerRelation> getWeakDirectedInequalities() {
        return new LinkedHashSet<IntegerRelation>(this.weakinequalities);
    }

    @Override
    public int hashCode() {
        int res = 97;
        for (IntegerRelation rel : this) {
            res += 3 * rel.hashCode();
        }
        return res;
    }

    @Override
    public boolean isEmpty() {
        return
            this.equations.isEmpty()
            && this.inequalities.isEmpty()
            && this.strictinequalities.isEmpty()
            && this.weakinequalities.isEmpty();
    }

    @Override
    public Iterator<IntegerRelation> iterator() {
        return
            new Iterator<IntegerRelation>() {

                private final Iterator<IntegerRelation> eqs = IntegerRelationSet.this.equations.iterator();
                private final Iterator<IntegerRelation> ineqs = IntegerRelationSet.this.inequalities.iterator();
                private Integer recent;
                private final Iterator<IntegerRelation> strict = IntegerRelationSet.this.strictinequalities.iterator();
                private final Iterator<IntegerRelation> weak = IntegerRelationSet.this.weakinequalities.iterator();

                @Override
                public boolean hasNext() {
                    return this.eqs.hasNext() || this.ineqs.hasNext() || this.strict.hasNext() || this.weak.hasNext();
                }

                @Override
                public IntegerRelation next() {
                    if (this.eqs.hasNext()) {
                        this.recent = IntegerRelationSet.EQUATIONS;
                        return this.eqs.next();
                    } else if (this.ineqs.hasNext()) {
                        this.recent = IntegerRelationSet.INEQUATIONS;
                        return this.ineqs.next();
                    } else if (this.strict.hasNext()) {
                        this.recent = IntegerRelationSet.STRICT_INEQUATIONS;
                        return this.strict.next();
                    } else if (this.weak.hasNext()) {
                        this.recent = IntegerRelationSet.WEAK_INEQUATIONS;
                        return this.weak.next();
                    } else {
                        throw new NoSuchElementException();
                    }
                }

                @Override
                public void remove() {
                    if (this.recent == null) {
                        throw new IllegalStateException("Next has not been called since last remove operation!");
                    }
                    switch (this.recent) {
                        case EQUATIONS:
                            this.eqs.remove();
                            break;
                        case INEQUATIONS:
                            this.ineqs.remove();
                            break;
                        case STRICT_INEQUATIONS:
                            this.strict.remove();
                            break;
                        case WEAK_INEQUATIONS:
                            this.weak.remove();
                            break;
                        default:
                            throw new IllegalStateException("Someone found a new way to build relations...");
                    }
                    this.recent = null;
                }

            };
    }

    @Override
    public boolean remove(Object o) {
        if (o instanceof IntegerRelation) {
            switch (((IntegerRelation)o).getRelationType()) {
                case EQ:
                    return this.equations.remove(o);
                case NE:
                    return this.inequalities.remove(o);
                case LT:
                case GT:
                    return this.strictinequalities.remove(o);
                case LE:
                case GE:
                    return this.weakinequalities.remove(o);
                default:
                    throw new IllegalStateException("Someone found a new way to build relations.");
            }
        }
        return false;
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        boolean res = false;
        for (Object o : c) {
            res |= this.remove(o);
        }
        return res;
    }

    /**
     * Removes all relations which contain the specified variable at an arbitrary position (e.g., if varName="a", then
     * a = b, z = 7 + a + c will be removed and relations like  c = d + e stay untouched).
     * @param var The variable.
     */
    public void removeRelations(Variable var) {
        Iterator<IntegerRelation> itr = this.iterator();
        while (itr.hasNext()) {
            IntegerRelation actRelation = itr.next();
            if (actRelation.getVariables().contains(var)) {
                itr.remove();
            }
        }
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        Iterator<IntegerRelation> itr = this.iterator();
        boolean res = false;
        while (itr.hasNext()) {
            if (!c.contains(itr.next())) {
                itr.remove();
                res = true;
            }
        }
        return res;
    }

    @Override
    public int size() {
        return
            this.equations.size()
            + this.inequalities.size()
            + this.strictinequalities.size()
            + this.weakinequalities.size();
    }

    @Override
    public Object[] toArray() {
        IntegerRelation[] res = new IntegerRelation[this.size()];
        int i = 0;
        for (IntegerRelation rel : this) {
            res[i] = rel;
            i++;
        }
        return res;
    }

    @SuppressWarnings("unchecked")
    @Override
    public <T> T[] toArray(T[] a) {
        T[] res;
        if (a.length >= this.size()) {
            res = a;
        } else {
            res = (T[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), this.size());
        }
        int i = 0;
        for (IntegerRelation rel : this) {
            res[i] = (T)rel;
            i++;
        }
        return res;
    }

    /**
     * Creates an SMT expression from this relation set.
     * @return An SMT expression representing the conjunction of the relations in this set.
     */
    @Override
    public SMTExpression<SBool> toSMTExp() {
        List<SMTExpression<SBool>> relations = new ArrayList<SMTExpression<SBool>>();
        for (IntegerRelation r : this) {
            relations.add(r.toSMTExp());
        }
        return Core.and(relations);
    }

    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder("{pure inequalities:\n");
        for (IntegerRelation rel : this.inequalities) {
            strBuilder.append("\t" + rel + "\n");
        }
        strBuilder.append("equations:\n");
        for (IntegerRelation rel : this.equations) {
            strBuilder.append("\t" + rel + "\n");
        }
        strBuilder.append("weak directed inequalities:\n");
        for (IntegerRelation rel : this.weakinequalities) {
            strBuilder.append("\t" + rel + "\n");
        }
        strBuilder.append("strict directed inequalities:\n");
        for (IntegerRelation rel : this.strictinequalities) {
            strBuilder.append("\t" + rel + "\n");
        }
        strBuilder.append("}\n");
        return strBuilder.toString();
    }

}
