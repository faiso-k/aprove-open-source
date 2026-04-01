package aprove.verification.oldframework.Algebra.Orders.Utility;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/** Implementation of a multiset of multiterms.
 *
 *  @author  Stephan Falke
 */

public class MultisetOfMultiterms {
    private final Hashtable multiset;

    /* constructros */

    private MultisetOfMultiterms() {
        this.multiset = new Hashtable();
    }

    /** Returns a new instance of <code>MultisetOfMultiterms</code>.
     */
    public static MultisetOfMultiterms create() {
        return new MultisetOfMultiterms();
    }

    /** Returns a new instance of <code>MultisetOfMultiterms</code>,
     * assuming that all function symbols have multiset status.
     * @param elements   a multiset of terms that'll be transformed into
     *                    multiterms
     * @see Multiterm#create(AlgebraTerm)
     */
    public static MultisetOfMultiterms create(final MultisetOfTerms elements) {
        final MultisetOfMultiterms res = MultisetOfMultiterms.create();
        final Enumeration e = elements.elements();
        AlgebraTerm t;

        while (e.hasMoreElements()) {
            t = (AlgebraTerm) e.nextElement();
            res.add(Multiterm.create(t), elements.numberOfOccurences(t));
        }

        return res;
    }

    /** Returns a new instance of <code>MultisetOfMultiterms</code>, giving
     * multiset status to those function symbols that have it according
     * to a status map.
     * @param elements   a multiset of terms that'll be transformed into
     *                    multiterms
     * @param map  the status map for the transformations
     * @see Multiterm#create(AlgebraTerm, StatusMap)
     */
    public static MultisetOfMultiterms create(final MultisetOfTerms elements, final StatusMap map) {
        final MultisetOfMultiterms res = MultisetOfMultiterms.create();
        final Enumeration e = elements.elements();
        AlgebraTerm t;

        while (e.hasMoreElements()) {
            t = (AlgebraTerm) e.nextElement();
            res.add(Multiterm.create(t, map), elements.numberOfOccurences(t));
        }

        return res;
    }

    /** Returns a new instance of <code>MultisetOfMultiterms</code>,
     * assuming that all function symbols have multiset status.
     * @param elements   a multiset of terms that'll be transformed into
     *                    multiterms
     * @param equiv  the qoset used for creation of the multiterms
     * @see Multiterm#create(AlgebraTerm, Qoset)
     */
    public static MultisetOfMultiterms create(final MultisetOfTerms elements, final Qoset equiv) {
        final MultisetOfMultiterms res = MultisetOfMultiterms.create();
        final Enumeration e = elements.elements();
        AlgebraTerm t;

        while (e.hasMoreElements()) {
            t = (AlgebraTerm) e.nextElement();
            res.add(Multiterm.create(t, equiv), elements.numberOfOccurences(t));
        }

        return res;
    }

    /** Returns a new instance of <code>MultisetOfMultiterms</code>, giving
     * multiset status to those function symbols that have it according
     * to a status map.
     * @param elements   a multiset of terms that'll be transformed into
     *                    multiterms
     * @param map  the status map for the transformations
     * @param equiv the qoset used for the transformations
     * @see Multiterm#create(AlgebraTerm, StatusMap)
     */
    public static MultisetOfMultiterms create(final MultisetOfTerms elements, final StatusMap map, final Qoset equiv) {
        final MultisetOfMultiterms res = MultisetOfMultiterms.create();
        final Enumeration e = elements.elements();
        AlgebraTerm t;

        while (e.hasMoreElements()) {
            t = (AlgebraTerm) e.nextElement();
            res.add(Multiterm.create(t, map, equiv), elements.numberOfOccurences(t));
        }

        return res;
    }

    /* returns the multiterm that represents o in the hashtable */
    private Multiterm getRep(final Multiterm o) {
        final Enumeration e = this.elements();
        Multiterm m = null;
        while (e.hasMoreElements()) {
            m = (Multiterm) e.nextElement();
            if (m.equals(o)) {
                return m;
            }
        }
        return null;
    }

    /** Adds the element <code>o</code> to this multiset.
     */
    public void add(final Multiterm o) {
        this.add(o, 1);
    }

    /** Adds <code>occ</code> occurences of the element <code>o</code> to
     * this multiset.
     */
    public void add(final Multiterm o, int occ) {
        final Multiterm m = this.getRep(o);
        if (m != null) {
            occ += this.numberOfOccurences(m);
            this.multiset.put(m, Integer.valueOf(occ));
        } else {
            this.multiset.put(o, Integer.valueOf(occ));
        }
    }

    /** Removes one occurence of <code>o</code> from this multiset.
     */
    public void remove(final Multiterm o) {
        final Multiterm m = this.getRep(o);
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
    public int numberOfOccurences(final Multiterm o) {
        final Multiterm m = this.getRep(o);
        if (m != null) {
            return ((Integer) this.multiset.get(m)).intValue();
        } else {
            return 0;
        }
    }

    /** Returns <code>true</code> if <code>o</code> occurrs at least once in
     * this multiset, <code>false</code> otherwise.
     */
    public boolean contains(final Multiterm o) {
        return this.getRep(o) != null;
    }

    /** Returns a new <code>MultisetOfMultiterms</code> that is the union of
     * this multiset and the multiset <code>other</code>.
     */
    public MultisetOfMultiterms union(final MultisetOfMultiterms other) {
        final MultisetOfMultiterms res = this.deepcopy();
        Enumeration e;
        Multiterm o;

        e = other.elements();
        while (e.hasMoreElements()) {
            o = (Multiterm) e.nextElement();
            res.add(o, other.numberOfOccurences(o));
        }

        return res;
    }

    /** Returns a new <code>MultisetOfMultiterms</code> that is the
     * intersection of this multiset and the multiset <code>other</code>.
     */
    public MultisetOfMultiterms intersect(final MultisetOfMultiterms other) {
        final MultisetOfMultiterms res = MultisetOfMultiterms.create();
        Enumeration e;
        Multiterm o;
        int occ1, occ2;
        int occ;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (Multiterm) e.nextElement();
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

    /** Returns a new <code>MultisetOfMultiterms</code> that contains the
     * elements from this multiset that are not in the multiset
     * <code>other</code>.
     */
    public MultisetOfMultiterms subtract(final MultisetOfMultiterms other) {
        final MultisetOfMultiterms res = MultisetOfMultiterms.create();
        Enumeration e;
        Multiterm o;
        int occ;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (Multiterm) e.nextElement();
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
    public MultisetOfMultiterms deepcopy() {
        final MultisetOfMultiterms res = MultisetOfMultiterms.create();
        Enumeration e;
        Multiterm o;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (Multiterm) e.nextElement();
            res.add(o.deepcopy(), this.numberOfOccurences(o));
        }

        return res;
    }

    /** Returns <code>true</code> if this multiset and the multiset
     * <code>other</code> contain the same elements with the same multiplicity,
     * returns <code>false</code> otherwise.
     */
    public boolean equals(final MultisetOfMultiterms other) {
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
        final MultisetOfMultiterms other = (MultisetOfMultiterms) obj;
        return this.equals(other);
    }

    /** Returns <code>true</code> if this multiset is contained in the multiset
     * <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean isContainedIn(final MultisetOfMultiterms other) {
        return this.subtract(other).multiset.isEmpty();
    }

    /** Returns <code>true</code> if this multiset is strictly contained in
     * the multiset <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean isStrictlyContainedIn(final MultisetOfMultiterms other) {
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
}
