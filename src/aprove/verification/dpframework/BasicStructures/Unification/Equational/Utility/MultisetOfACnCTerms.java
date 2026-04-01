/*
 * Created on Jan 23, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility;

import java.util.*;

import immutables.*;

/**
 * Implements a multiset of ACnCTerms
 * @author Stephan Falke
 */

public class MultisetOfACnCTerms implements Immutable {
    private final Hashtable<ACnCTerm, Integer> multiset;

    private MultisetOfACnCTerms(final ArrayList<ACnCTerm> multiArrayList) {
        this.multiset = new Hashtable<ACnCTerm, Integer>();
        for (final ACnCTerm t : multiArrayList) {
            if (this.multiset.containsKey(t)) {
                this.multiset.put(t, Integer.valueOf(this.multiset.get(t) + 1));
            } else {
                this.multiset.put(t, Integer.valueOf(1));
            }
        }
    }

    /** Returns a new instance of <code>MultisetOfACTerms</code> as given in <code>multiArrayList</code>.
     */
    public static MultisetOfACnCTerms create(final ArrayList<ACnCTerm> multiArrayList) {
        return new MultisetOfACnCTerms(multiArrayList);
    }

    /** returns the term that represents o in the hashtable,
     * e.g. returns o iff multiset.containsKey(o) else null
     */
    private ACnCTerm getRep(final ACnCTerm o) {
        if (this.multiset.get(o) != null) {
            return o;
        } else {
            return null;
        }
    }

    /** Returns the number of occurences of <code>o</code> in this multiset.
     */
    public int numberOfOccurences(final ACnCTerm o) {
        final ACnCTerm m = this.getRep(o);
        if (m != null) {
            return (this.multiset.get(m)).intValue();
        } else {
            return 0;
        }
    }

    /** Returns <code>true</code> iff <code>o</code> occurrs at least once in
     * this multiset, <code>false</code> otherwise.
     */
    public boolean contains(final ACnCTerm o) {
        return this.getRep(o) != null;
    }

    /** Returns a new <code>MultisetOfTerms</code> that is the union of this
     * multiset and the multiset <code>other</code>.
     */
    public MultisetOfACnCTerms union(final MultisetOfACnCTerms other) {
        final ArrayList<ACnCTerm> multiVec = this.toRealTermArrayList();
        final ArrayList<ACnCTerm> otherVec = other.toRealTermArrayList();

        for (final ACnCTerm t : otherVec) {
            multiVec.add(t);
        }

        return MultisetOfACnCTerms.create(multiVec);
    }

    /** Returns a new <code>MultisetOfTerms</code> that is the intersection of
     * this multiset and the multiset <code>other</code>.
     */
    public MultisetOfACnCTerms intersect(final MultisetOfACnCTerms other) {
        final ArrayList<ACnCTerm> res = new ArrayList<ACnCTerm>();
        int occ1, occ2;
        int occ;

        for (final ACnCTerm t : other.toTermArrayList()) {
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

        return MultisetOfACnCTerms.create(res);
    }

    /** Returns a new <code>MultisetOfTerms</code> that contains the elements
     * from this multiset that are not in the multiset <code>other</code>.
     */
    public MultisetOfACnCTerms subtract(final MultisetOfACnCTerms other) {
        final ArrayList<ACnCTerm> res = new ArrayList<ACnCTerm>();
        int occ;

        for (final ACnCTerm t : this.toTermArrayList()) {
            occ = this.numberOfOccurences(t) - other.numberOfOccurences(t);
            for (int i = 0; i < occ; i++) {
                res.add(t);
            }
        }

        return MultisetOfACnCTerms.create(res);
    }

    /** Returns a deep copy of this multiset.
     */
    public MultisetOfACnCTerms deepcopy() {
        final ArrayList<ACnCTerm> res = new ArrayList<ACnCTerm>();

        for (final ACnCTerm t : this.toRealTermArrayList()) {
            res.add(t.deepcopy());
        }

        return MultisetOfACnCTerms.create(res);
    }

    /** Returns an <code>Enumeration</code> of the elements in this
     * multiset.
     * Each element occurs only once even if it is contained in
     * this multiset more than once.
     */
    public Set<ACnCTerm> elements() {
        return this.multiset.keySet();
    }

    /** Returns a shallow copy of this multiset.
     */
    public MultisetOfACnCTerms shallowcopy() {
        return MultisetOfACnCTerms.create(this.toRealTermArrayList());
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
    public ArrayList<ACnCTerm> toTermArrayList() {
        final ArrayList<ACnCTerm> res = new ArrayList<ACnCTerm>();
        for (final ACnCTerm t : this.multiset.keySet()) {
            res.add(t);
        }
        return res;
    }

    /** One copy of each entry, counting its
     * multiplicity.
     */
    public ArrayList<ACnCTerm> toRealTermArrayList() {
        final ArrayList<ACnCTerm> res = new ArrayList<ACnCTerm>();
        for (final ACnCTerm t : this.multiset.keySet()) {
            for (int i = 0; i < this.multiset.get(t); i++) {
                res.add(t);
            }
        }
        return res;
    }

}
