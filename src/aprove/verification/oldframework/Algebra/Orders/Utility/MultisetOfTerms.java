package aprove.verification.oldframework.Algebra.Orders.Utility;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Implementation of a multiset of terms.
 *
 *  @author  Stephan Falke
 */

public class MultisetOfTerms {
    private final Hashtable multiset;

    /* constructros */

    private MultisetOfTerms() {
        this.multiset = new Hashtable();
    }

    /** Returns a new instance of <code>MultisetOfTerms</code>.
     */
    public static MultisetOfTerms create() {
        return new MultisetOfTerms();
    }

    /** Returns a new instance of <code>MultisetOfTerms</code> constructed
     * from a term by applying flattening as needed for elementary
     * ACU-unification.
     */
    public static MultisetOfTerms createACU(final AlgebraTerm s) {
        MultisetOfTerms res = MultisetOfTerms.create();

        final Symbol symb = s.getSymbol();

        final Iterator i = s.getArguments().iterator();
        while (i.hasNext()) {
            final AlgebraTerm sub = (AlgebraTerm) i.next();
            if (sub.isVariable()) {
                res.add(sub);
            } else if (sub.isConstant()) {
                res.add(sub);
            } else {
                final SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol) sub.getSymbol();
                if (fun.equals(symb)) {
                    res = res.union(MultisetOfTerms.createACU(sub));
                }
            }
        }

        return res;
    }

    /** Returns a new instance of <code>MultisetOfTerms</code>.
     * @param elements   the members of the new multiset
     */
    public static MultisetOfTerms create(final List<AlgebraTerm> elements) {
        final MultisetOfTerms res = MultisetOfTerms.create();
        final Iterator i = elements.iterator();

        while (i.hasNext()) {
            res.add((AlgebraTerm) i.next());
        }

        return res;
    }

    /** Returns a new instance of <code>MultisetOfTerms</code>.
     * @param elements   a multiset of multiterms that'll be transformed into
     *                   terms
     */
    public static MultisetOfTerms create(final MultisetOfMultiterms elements) {
        final MultisetOfTerms res = MultisetOfTerms.create();
        final Enumeration e = elements.elements();
        Multiterm t;

        while (e.hasMoreElements()) {
            t = (Multiterm) e.nextElement();
            res.add(t.toTerm(), elements.numberOfOccurences(t));
        }

        return res;
    }

    /** Returns a new instance of <code>MultisetOfTerms</code>.
     * @param elements   a multiset of multiterms that'll be transformed into
     *                   terms
     */
    public static MultisetOfTerms create(final MultisetOfFlattenedMultiterms elements) {
        final MultisetOfTerms res = MultisetOfTerms.create();
        final Enumeration e = elements.elements();
        FlattenedMultiterm t;

        while (e.hasMoreElements()) {
            t = (FlattenedMultiterm) e.nextElement();
            res.add(t.toTerm(), elements.numberOfOccurences(t));
        }

        return res;
    }

    /** Returns a new instance of <code>MultisetOfTerms</code>.
     * @param elements   a multiset of multiterms that'll be transformed into
     *                   terms
     */
    public static MultisetOfTerms create(final MultisetOfFlattenedQuasiMultiterms elements) {
        final MultisetOfTerms res = MultisetOfTerms.create();
        final Enumeration e = elements.elements();
        FlattenedQuasiMultiterm t;

        while (e.hasMoreElements()) {
            t = (FlattenedQuasiMultiterm) e.nextElement();
            res.add(t.toTerm(), elements.numberOfOccurences(t));
        }

        return res;
    }

    /* returns the term that represents o in the hashtable */
    private AlgebraTerm getRep(final AlgebraTerm o) {
        if (this.multiset.get(o) != null) {
            return o;
        } else {
            return null;
        }
    }

    /** Adds the element <code>o</code> to this multiset.
     */
    public void add(final AlgebraTerm o) {
        this.add(o, 1);
    }

    /** Adds <code>occ</code> occurences of the element <code>o</code> to
     * this multiset.
     */
    public void add(final AlgebraTerm o, int occ) {
        final AlgebraTerm m = this.getRep(o);
        if (m != null) {
            occ += this.numberOfOccurences(m);
            this.multiset.put(m, Integer.valueOf(occ));
        } else {
            this.multiset.put(o, Integer.valueOf(occ));
        }
    }

    /** Removes one occurence of <code>o</code> from this multiset.
     */
    public void remove(final AlgebraTerm o) {
        final AlgebraTerm m = this.getRep(o);
        if (m != null) {
            int occ = this.numberOfOccurences(m);
            occ--;
            if (occ != 0) {
                this.multiset.put(m, Integer.valueOf(occ));
            } else {
                this.multiset.remove(m);
            }
        }
    }

    /** Removes all occurences of <code>o</code> from this multiset.
     */
    public void removeAll(final AlgebraTerm o) {
        final AlgebraTerm m = this.getRep(o);
        if (m != null) {
            this.multiset.remove(m);
        }
    }

    /** Returns the number of occurences of <code>o</code> in this multiset.
     */
    public int numberOfOccurences(final AlgebraTerm o) {
        final AlgebraTerm m = this.getRep(o);
        if (m != null) {
            return ((Integer) this.multiset.get(m)).intValue();
        } else {
            return 0;
        }
    }

    /** Returns <code>true</code> if <code>o</code> occurrs at least once in
     * this multiset, <code>false</code> otherwise.
     */
    public boolean contains(final AlgebraTerm o) {
        return this.getRep(o) != null;
    }

    /** Returns a new <code>MultisetOfTerms</code> that is the union of this
     * multiset and the multiset <code>other</code>.
     */
    public MultisetOfTerms union(final MultisetOfTerms other) {
        final MultisetOfTerms res = this.deepcopy();
        Enumeration e;
        AlgebraTerm o;

        e = other.elements();
        while (e.hasMoreElements()) {
            o = (AlgebraTerm) e.nextElement();
            res.add(o, other.numberOfOccurences(o));
        }

        return res;
    }

    /** Returns a new <code>MultisetOfTerms</code> that is the intersection of
     * this multiset and the multiset <code>other</code>.
     */
    public MultisetOfTerms intersect(final MultisetOfTerms other) {
        final MultisetOfTerms res = MultisetOfTerms.create();
        Enumeration e;
        AlgebraTerm o;
        int occ1, occ2;
        int occ;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (AlgebraTerm) e.nextElement();
            if (other.contains(o)) {
                occ1 = this.numberOfOccurences(o);
                occ2 = other.numberOfOccurences(o);
                if (occ1 < occ2) {
                    occ = occ1;
                } else {
                    occ = occ2;
                }
                res.add(o, occ);
            }
        }

        return res;
    }

    /** Returns a new <code>MultisetOfTerms</code> that contains the elements
     * from this multiset that are not in the multiset <code>other</code>.
     */
    public MultisetOfTerms subtract(final MultisetOfTerms other) {
        final MultisetOfTerms res = MultisetOfTerms.create();
        Enumeration e;
        AlgebraTerm o;
        int occ;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (AlgebraTerm) e.nextElement();
            occ = this.numberOfOccurences(o) - other.numberOfOccurences(o);
            if (occ > 0) {
                res.add(o, occ);
            }
        }

        return res;
    }

    /** Returns an <code>Enumeration</code> of the elements in this
     * multiset.
     * Each element occurs only once even if it is contained in
     * this multiset more than once.
     */
    public Enumeration elements() {
        return this.multiset.keys();
    }

    /** Returns a <code>Term</code> that is member of this multiset.
     */
    public AlgebraTerm getTerm() {
        return (AlgebraTerm) this.multiset.keys().nextElement();
    }

    /** Returns a deep copy of this multiset.
     */
    public MultisetOfTerms deepcopy() {
        final MultisetOfTerms res = MultisetOfTerms.create();
        Enumeration e;
        AlgebraTerm o;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (AlgebraTerm) e.nextElement();
            res.add(o.deepcopy(), this.numberOfOccurences(o));
        }

        return res;
    }

    /** Returns a shallow copy of this multiset.
     */
    public MultisetOfTerms shallowcopy() {
        final MultisetOfTerms res = MultisetOfTerms.create();
        Enumeration e;
        AlgebraTerm o;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (AlgebraTerm) e.nextElement();
            res.add(o, this.numberOfOccurences(o));
        }

        return res;
    }

    /** Returns <code>true</code> if this multiset and the multiset
     * <code>other</code> contain the same elements with the same multiplicity,
     * returns <code>false</code> otherwise.
     */
    public boolean equals(final MultisetOfTerms other) {
        return this.subtract(other).multiset.isEmpty() && other.subtract(this).multiset.isEmpty();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final MultisetOfTerms other = (MultisetOfTerms) obj;
        return this.equals(other);
    }

    /** Returns <code>true</code> if this multiset is contained in the multiset
     * <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean isContainedIn(final MultisetOfTerms other) {
        return this.subtract(other).multiset.isEmpty();
    }

    /** Returns <code>true</code> if this multiset is strictly contained in
     * the multiset <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean isStrictlyContainedIn(final MultisetOfTerms other) {
        return this.subtract(other).multiset.isEmpty() && !other.subtract(this).multiset.isEmpty();
    }

    /** Returns <code>true</code> if this multiset contains no elements,
     * returns <code>false</code> otherwise.
     */
    public boolean isEmpty() {
        return this.multiset.isEmpty();
    }

    /** Returns the number of elements in this multiset, not counting their
     * multiplicity.
     */
    public int size() {
        return this.multiset.size();
    }

    /** Returns a <code>Vector<Term></code> containing the elements of
     * this multiset with their multiplicity.
     */
    public Vector<AlgebraTerm> toVector() {
        final Vector<AlgebraTerm> res = new Vector<AlgebraTerm>();
        final Iterator i = this.multiset.keySet().iterator();
        int j;
        int n;
        AlgebraTerm t;
        while (i.hasNext()) {
            t = (AlgebraTerm) i.next();
            n = this.numberOfOccurences(t);
            for (j = 0; j < n; j++) {
                res.add(t);
            }
        }
        return res;
    }

    /** Returns a string representation of this multiset.
     */
    @Override
    public String toString() {
        return this.multiset.toString();
    }

}
