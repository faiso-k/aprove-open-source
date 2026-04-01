package aprove.verification.oldframework.Unification.Utility;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/** Implementation of a multiset of AC-and-C-terms.
 *
 *  @author  Stephan Falke
 *  @version $Id$
 */

public class MultisetOfACnCTerms {
    private final Hashtable multiset;

    /* constructros */

    private MultisetOfACnCTerms() {
        this.multiset = new Hashtable();
    }

    /** Returns a new instance of <code>MultisetOfACnCTerms</code>.
     */
    public static MultisetOfACnCTerms create() {
        return new MultisetOfACnCTerms();
    }

    /* returns the term that represents o in the hashtable */
    private ACnCTerm getRep(final ACnCTerm o) {
        if (this.multiset.get(o) != null) {
            return o;
        } else {
            return null;
        }
    }

    /** Adds the element <code>o</code> to this multiset.
     */
    public void add(final ACnCTerm o) {
        this.add(o, 1);
    }

    /** Adds <code>occ</code> occurences of the element <code>o</code> to
     * this multiset.
     */
    public void add(final ACnCTerm o, int occ) {
        final ACnCTerm m = this.getRep(o);
        if (m != null) {
            occ += this.numberOfOccurences(m);
            this.multiset.put(m, Integer.valueOf(occ));
        } else {
            this.multiset.put(o, Integer.valueOf(occ));
        }
    }

    /** Removes one occurence of <code>o</code> from this multiset.
     */
    public void remove(final ACnCTerm o) {
        final ACnCTerm m = this.getRep(o);
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
    public void removeAll(final ACnCTerm o) {
        final ACnCTerm m = this.getRep(o);
        if (m != null) {
            this.multiset.remove(m);
        }
    }

    /** Returns the number of occurences of <code>o</code> in this multiset.
     */
    public int numberOfOccurences(final ACnCTerm o) {
        final ACnCTerm m = this.getRep(o);
        if (m != null) {
            return ((Integer) this.multiset.get(m)).intValue();
        } else {
            return 0;
        }
    }

    /** Returns <code>true</code> if <code>o</code> occurrs at least once in
     * this multiset, <code>false</code> otherwise.
     */
    public boolean contains(final ACnCTerm o) {
        return this.getRep(o) != null;
    }

    /** Returns a new <code>MultisetOfTerms</code> that is the union of this
     * multiset and the multiset <code>other</code>.
     */
    public MultisetOfACnCTerms union(final MultisetOfACnCTerms other) {
        final MultisetOfACnCTerms res = this.deepcopy();
        Enumeration e;
        ACnCTerm o;

        e = other.elements();
        while (e.hasMoreElements()) {
            o = (ACnCTerm) e.nextElement();
            res.add(o, other.numberOfOccurences(o));
        }

        return res;
    }

    /** Returns a new <code>MultisetOfTerms</code> that is the intersection of
     * this multiset and the multiset <code>other</code>.
     */
    public MultisetOfACnCTerms intersect(final MultisetOfACnCTerms other) {
        final MultisetOfACnCTerms res = MultisetOfACnCTerms.create();
        Enumeration e;
        ACnCTerm o;
        int occ1, occ2;
        int occ;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (ACnCTerm) e.nextElement();
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
    public MultisetOfACnCTerms subtract(final MultisetOfACnCTerms other) {
        final MultisetOfACnCTerms res = MultisetOfACnCTerms.create();
        Enumeration e;
        ACnCTerm o;
        int occ;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (ACnCTerm) e.nextElement();
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
    public MultisetOfACnCTerms deepcopy() {
        final MultisetOfACnCTerms res = MultisetOfACnCTerms.create();
        Enumeration e;
        ACnCTerm o;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (ACnCTerm) e.nextElement();
            res.add(o.deepcopy(), this.numberOfOccurences(o));
        }

        return res;
    }

    /** Returns a shallow copy of this multiset.
     */
    public MultisetOfACnCTerms shallowcopy() {
        final MultisetOfACnCTerms res = MultisetOfACnCTerms.create();
        Enumeration e;
        ACnCTerm o;

        e = this.elements();
        while (e.hasMoreElements()) {
            o = (ACnCTerm) e.nextElement();
            res.add(o, this.numberOfOccurences(o));
        }

        return res;
    }

    /** Returns <code>true</code> if this multiset and the multiset
     * <code>other</code> contain the same elements with the same multiplicity,
     * returns <code>false</code> otherwise.
     */
    public boolean equals(final MultisetOfACnCTerms other) {
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
        final MultisetOfACnCTerms other = (MultisetOfACnCTerms) obj;
        return this.equals(other);
    }

    /** Returns <code>true</code> if this multiset is contained in the multiset
     * <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean isContainedIn(final MultisetOfACnCTerms other) {
        return this.subtract(other).multiset.isEmpty();
    }

    /** Returns <code>true</code> if this multiset is strictly contained in
     * the multiset <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean isStrictlyContainedIn(final MultisetOfACnCTerms other) {
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

    /** Returns the number of elements in this multiset, taking their
     * multiplicity into account.
     */
    public int realSize() {
        int res = 0;
        final Enumeration e = this.elements();
        while (e.hasMoreElements()) {
            res += this.numberOfOccurences((ACnCTerm) e.nextElement());
        }
        return res;
    }

    /** Returns a string representation of this multiset.
     */
    @Override
    public String toString() {
        return this.multiset.toString();
    }

    /** One copy of each entry.
     */
    public List<AlgebraTerm> toTermList() {
        final List<AlgebraTerm> res = new Vector<AlgebraTerm>();
        final Iterator i = this.multiset.keySet().iterator();
        while (i.hasNext()) {
            res.add(((ACnCTerm) i.next()).toTerm());
        }
        return res;
    }

    /** Returns a list containing the elements with their multiplicity.
     */
    public List<ACnCTerm> toList() {
        final List<ACnCTerm> res = new Vector<ACnCTerm>();
        final Iterator i = this.multiset.keySet().iterator();
        while (i.hasNext()) {
            final ACnCTerm elem = (ACnCTerm) i.next();
            for (int j = 0; j < this.numberOfOccurences(elem); j++) {
                res.add(elem);
            }
        }
        return res;
    }

}
