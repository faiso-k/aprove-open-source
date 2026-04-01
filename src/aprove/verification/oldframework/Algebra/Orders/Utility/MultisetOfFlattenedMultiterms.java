package aprove.verification.oldframework.Algebra.Orders.Utility;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/** Implementation of a multiset of flattened multiterms.
 *
 *  @author  Stephan Falke
 */

public class MultisetOfFlattenedMultiterms {
    private final Hashtable multiset;

    /* constructros */

    private MultisetOfFlattenedMultiterms() {
        this.multiset = new Hashtable();
    }

    /** Returns a new instance of <code>MultisetOfFlattenedMultiterms</code>.
     */
    public static MultisetOfFlattenedMultiterms create() {
        return new MultisetOfFlattenedMultiterms();
    }

    /** Returns a new instance of <code>FlattenedMultisetOfMultiterms</code>, giving
     * multiset status to those function symbols that have it according
     * to a status map.
     * @param elements   a multiset of terms that'll be transformed into
     *                    multiterms
     * @param map  the status map for the transformations
     * @see FlattenedMultiterm#create(AlgebraTerm, StatusMap)
     */
    public static MultisetOfFlattenedMultiterms create(final MultisetOfTerms elements, final StatusMap map) {
        final MultisetOfFlattenedMultiterms res = MultisetOfFlattenedMultiterms.create();
        final Enumeration e = elements.elements();
        AlgebraTerm t;

        while (e.hasMoreElements()) {
            t = (AlgebraTerm) e.nextElement();
            res.add(FlattenedMultiterm.create(t, map), elements.numberOfOccurences(t));
        }

        return res;
    }

    /* returns the multiterm that represents o in the hashtable */
    private FlattenedMultiterm getRep(final FlattenedMultiterm o) {
        final Enumeration e = this.elements();
        FlattenedMultiterm m = null;
        while (e.hasMoreElements()) {
            m = (FlattenedMultiterm) e.nextElement();
            if (m.equals(o)) {
                return m;
            }
        }
        return null;
    }

    /** Adds the element <code>o</code> to this multiset.
     */
    public void add(final FlattenedMultiterm o) {
        this.add(o, 1);
    }

    /** Adds <code>occ</code> occurences of the element <code>o</code> to
     * this multiset.
     */
    public void add(final FlattenedMultiterm o, int occ) {
        final FlattenedMultiterm m = this.getRep(o);
        if (m != null) {
            occ += this.numberOfOccurences(m);
            this.multiset.put(m, Integer.valueOf(occ));
        } else {
            this.multiset.put(o, Integer.valueOf(occ));
        }
    }

    /** Removes one occurence of <code>o</code> from this multiset.
     */
    public void remove(final FlattenedMultiterm o) {
        final FlattenedMultiterm m = this.getRep(o);
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

    /** Returns the number of occurences of <code>o</code> in this multiset.
     */
    public int numberOfOccurences(final FlattenedMultiterm o) {
        final FlattenedMultiterm m = this.getRep(o);
        if (m != null) {
            return ((Integer) this.multiset.get(m)).intValue();
        } else {
            return 0;
        }
    }

    /** Returns <code>true</code> if <code>o</code> occurrs at least once in
     * this multiset, <code>false</code> otherwise.
     */
    public boolean contains(final FlattenedMultiterm o) {
        return this.getRep(o) != null;
    }

    /** Returns a new <code>MultisetOfFlattenedMultiterms</code> that is the union of
     * this multiset and the multiset <code>other</code>.
     */
    public MultisetOfFlattenedMultiterms union(final MultisetOfFlattenedMultiterms other) {
        final MultisetOfFlattenedMultiterms res = this.deepcopy();
        Enumeration e;
        FlattenedMultiterm o;

        e = other.elements();
        while (e.hasMoreElements()) {
            o = (FlattenedMultiterm) e.nextElement();
            res.add(o, other.numberOfOccurences(o));
        }

        return res;
    }

    /** Returns a new <code>MultisetOfFlattenedMultiterms</code> that is the
     * intersection of this multiset and the multiset <code>other</code>.
     */
    public MultisetOfFlattenedMultiterms intersect(final MultisetOfFlattenedMultiterms other) {
        final MultisetOfFlattenedMultiterms res = MultisetOfFlattenedMultiterms.create();
        Enumeration e;
        FlattenedMultiterm o;
        int occ1, occ2;
        int occ;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (FlattenedMultiterm) e.nextElement();
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

    /** Returns a new <code>MultisetOfFlattenedMultiterms</code> that contains the
     * elements from this multiset that are not in the multiset
     * <code>other</code>.
     */
    public MultisetOfFlattenedMultiterms subtract(final MultisetOfFlattenedMultiterms other) {
        final MultisetOfFlattenedMultiterms res = MultisetOfFlattenedMultiterms.create();
        Enumeration e;
        FlattenedMultiterm o;
        int occ;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (FlattenedMultiterm) e.nextElement();
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

    /** Returns a deep copy of this multiset.
     */
    public MultisetOfFlattenedMultiterms deepcopy() {
        final MultisetOfFlattenedMultiterms res = MultisetOfFlattenedMultiterms.create();
        Enumeration e;
        FlattenedMultiterm o;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (FlattenedMultiterm) e.nextElement();
            res.add(o.deepcopy(), this.numberOfOccurences(o));
        }

        return res;
    }

    /** Returns <code>true</code> if this multiset and the multiset
     * <code>other</code> contain the same elements with the same multiplicity,
     * returns <code>false</code> otherwise.
     */
    public boolean equals(final MultisetOfFlattenedMultiterms other) {
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
        final MultisetOfFlattenedMultiterms other = (MultisetOfFlattenedMultiterms) obj;
        return this.equals(other);
    }

    /** Returns <code>true</code> if this multiset is contained in the multiset
     * <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean isContainedIn(final MultisetOfFlattenedMultiterms other) {
        return this.subtract(other).multiset.isEmpty();
    }

    /** Returns <code>true</code> if this multiset is strictly contained in
     * the multiset <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean isStrictlyContainedIn(final MultisetOfFlattenedMultiterms other) {
        return this.subtract(other).multiset.isEmpty() && !other.subtract(this).multiset.isEmpty();
    }

    /** Returns <code>true</code> if this multiset contains no elements,
     * returns <code>false</code> otherwise.
     */
    public boolean isEmpty() {
        return this.multiset.isEmpty();
    }

    /** Returns a string representation of this multiset.
     */
    @Override
    public String toString() {
        return this.multiset.toString();
    }

    /** Returns a <code>Vector<Term></code> containing the elements of
     * this multiset with their multiplicity.
     */
    public Vector<AlgebraTerm> toTermVector() {
        final Vector<AlgebraTerm> res = new Vector<AlgebraTerm>();
        final Iterator i = this.multiset.keySet().iterator();
        int j;
        int n;
        FlattenedMultiterm t;
        AlgebraTerm tt;
        while (i.hasNext()) {
            t = (FlattenedMultiterm) i.next();
            tt = t.toTerm();
            n = this.numberOfOccurences(t);
            for (j = 0; j < n; j++) {
                res.add(tt);
            }
        }
        return res;
    }

    /** Returns a <code>Vector<Term></code> containing the elements of
     * this multiset, but copy of each.
     */
    public Vector<AlgebraTerm> toUniqueTermVector() {
        final Vector<AlgebraTerm> res = new Vector<AlgebraTerm>();
        final Iterator i = this.multiset.keySet().iterator();
        FlattenedMultiterm t;
        AlgebraTerm tt;
        while (i.hasNext()) {
            t = (FlattenedMultiterm) i.next();
            tt = t.toTerm();
            res.add(tt);
        }
        return res;
    }

}
