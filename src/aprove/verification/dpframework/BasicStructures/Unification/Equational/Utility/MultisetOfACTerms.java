/*
 * Created on Jan 23, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility;

import java.util.*;

import immutables.*;

/**
 * Implements a multiset of ACTerms
 * @author Stephan Falke
 */

public class MultisetOfACTerms implements Immutable {
    private final Hashtable<ACTerm, Integer> multiset;

    private MultisetOfACTerms(final ArrayList<ACTerm> multiArrayList) {
        this.multiset = new Hashtable<ACTerm, Integer>();
        for (final ACTerm t : multiArrayList) {
            if (this.multiset.containsKey(t)) {
                this.multiset.put(t, Integer.valueOf(this.multiset.get(t) + 1));
            } else {
                this.multiset.put(t, Integer.valueOf(1));
            }
        }
    }

    /** Returns a new instance of <code>MultisetOfACTerms</code> as given in <code>multiArrayList</code>.
     */
    public static MultisetOfACTerms create(final ArrayList<ACTerm> multiArrayList) {
        return new MultisetOfACTerms(multiArrayList);
    }

    /** returns the term that represents o in the hashtable,
     * e.g. returns o iff multiset.containsKey(o) else null
     */
    private ACTerm getRep(final ACTerm o) {
        if (this.multiset.get(o) != null) {
            return o;
        } else {
            return null;
        }
    }

    /** Returns the number of occurences of <code>o</code> in this multiset.
     */
    public int numberOfOccurences(final ACTerm o) {
        final ACTerm m = this.getRep(o);
        if (m != null) {
            return (this.multiset.get(m)).intValue();
        } else {
            return 0;
        }
    }

    /** Returns <code>true</code> iff <code>o</code> occurrs at least once in
     * this multiset, <code>false</code> otherwise.
     */
    public boolean contains(final ACTerm o) {
        return this.getRep(o) != null;
    }

    /** Returns a new <code>MultisetOfTerms</code> that is the union of this
     * multiset and the multiset <code>other</code>.
     */
    public MultisetOfACTerms union(final MultisetOfACTerms other) {
        final ArrayList<ACTerm> multiVec = this.toRealTermArrayList();
        final ArrayList<ACTerm> otherVec = other.toRealTermArrayList();

        for (final ACTerm t : otherVec) {
            multiVec.add(t);
        }

        return MultisetOfACTerms.create(multiVec);
    }

    /** Returns a new <code>MultisetOfTerms</code> that is the intersection of
     * this multiset and the multiset <code>other</code>.
     */
    public MultisetOfACTerms intersect(final MultisetOfACTerms other) {
        final ArrayList<ACTerm> res = new ArrayList<ACTerm>();
        int occ1, occ2;
        int occ;

        for (final ACTerm t : other.toTermArrayList()) {
            if (this.contains(t)) {
                occ1 = this.numberOfOccurences(t);
                occ2 = other.numberOfOccurences(t);
                if (occ1 < occ2) {
                    occ = occ1;
                } else {
                    occ = occ2;
                }
                for (int i = 0; i < occ; i++) {
                    res.add(t);
                }
            }
        }

        return MultisetOfACTerms.create(res);
    }

    /** Returns a new <code>MultisetOfTerms</code> that contains the elements
     * from this multiset that are not in the multiset <code>other</code>.
     */
    public MultisetOfACTerms subtract(final MultisetOfACTerms other) {
        final ArrayList<ACTerm> res = new ArrayList<ACTerm>();
        int occ;
        for (final ACTerm t : this.toTermArrayList()) {
            occ = this.numberOfOccurences(t) - other.numberOfOccurences(t);
            for (int i = 0; i < occ; i++) {
                res.add(t);
            }
        }

        return MultisetOfACTerms.create(res);
    }

    /** Returns an <code>Enumeration</code> of the elements in this
     * multiset.
     * Each element occurs only once even if it is contained in
     * this multiset more than once.
     */
    public Set<ACTerm> elements() {
        return this.multiset.keySet();
    }

    /** Returns a shallow copy of this multiset.
     */
    public MultisetOfACTerms shallowcopy() {
        return MultisetOfACTerms.create(this.toRealTermArrayList());
    }

    /** Returns <code>true</code> if this multiset and the multiset
     * <code>other</code> contain the same elements with the same multiplicity,
     * returns <code>false</code> otherwise.
     */
    public boolean equals(final MultisetOfACTerms other) {
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
        final MultisetOfACTerms other = (MultisetOfACTerms) obj;
        return this.equals(other);
    }

    /** Returns <code>true</code> if this multiset is contained in the multiset
     * <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean isContainedIn(final MultisetOfACTerms other) {
        return this.subtract(other).multiset.isEmpty();
    }

    /** Returns <code>true</code> if this multiset is strictly contained in
     * the multiset <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean isStrictlyContainedIn(final MultisetOfACTerms other) {
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
        return this.toRealTermArrayList().size();
    }

    /** Returns a string representation of this multiset.
     */
    @Override
    public String toString() {
        return this.multiset.toString();
    }

    /** One copy of each entry, not counting its
     * multiplicity.
     */
    public ArrayList<ACTerm> toTermArrayList() {
        final ArrayList<ACTerm> res = new ArrayList<ACTerm>();
        for (final ACTerm t : this.multiset.keySet()) {
            res.add(t);
        }
        return res;
    }

    /** One copy of each entry, counting its
     * multiplicity.
     */
    public ArrayList<ACTerm> toRealTermArrayList() {
        final ArrayList<ACTerm> res = new ArrayList<ACTerm>();
        for (final ACTerm t : this.multiset.keySet()) {
            for (int i = 0; i < this.multiset.get(t); i++) {
                res.add(t);
            }
        }
        return res;
    }

}
