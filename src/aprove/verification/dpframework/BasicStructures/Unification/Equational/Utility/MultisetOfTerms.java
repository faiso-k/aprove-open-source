/*
 * Created on Feb 10, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

/** Implementation of a multiset of terms. *
 *  @author  Stephan Falke
 */

public class MultisetOfTerms implements Immutable {
    private final Hashtable<TRSTerm, Integer> multiset;

    /* constructors */

    private MultisetOfTerms(final Vector<TRSTerm> multiVector) {
        this.multiset = new Hashtable<TRSTerm, Integer>();
        for (final TRSTerm t : multiVector) {
            if (this.multiset.containsKey(t)) {
                this.multiset.put(t, Integer.valueOf(this.multiset.get(t) + 1));
            } else {
                this.multiset.put(t, Integer.valueOf(1));
            }
        }
    }

    private MultisetOfTerms(final TRSTerm s) {
        final Hashtable<TRSTerm, Integer> multiset = new Hashtable<TRSTerm, Integer>();

        this.multiset = this.constructACUMultiset(multiset, s);
    }

    private Hashtable<TRSTerm, Integer> constructACUMultiset(final Hashtable<TRSTerm, Integer> multiset, final TRSTerm s) {
        if (s instanceof TRSVariable) {
            multiset.put(s, 1);
        } else {
            for (final TRSTerm sub : ((TRSFunctionApplication) s).getArguments()) {
                if (sub.isVariable() || ((TRSFunctionApplication) sub).getArguments().size() == 0) {
                    if (multiset.containsKey(sub)) {
                        multiset.put(sub, Integer.valueOf(multiset.get(sub) + 1));
                    } else {
                        multiset.put(sub, Integer.valueOf(1));
                    }
                } else {
                    if (((TRSFunctionApplication) s).getRootSymbol().equals(((TRSFunctionApplication) sub).getRootSymbol())) {
                        multiset.putAll(this.constructACUMultiset(multiset, sub));
                    }
                }
            }
        }
        return multiset;
    }

    /** Returns a new instance of <code>MultisetOfACTerms</code> as given in <code>multiVector</code>.
     */
    public static MultisetOfTerms create(final Vector<TRSTerm> multiVector) {
        return new MultisetOfTerms(multiVector);
    }

    /** Returns a new instance of <code>MultisetOfTerms</code> constructed
     * from a term by applying flattening as needed for elementary
     * ACU-unification.
     */
    public static MultisetOfTerms createACU(final TRSTerm s) {
        return new MultisetOfTerms(s);
    }

    /** returns the term that represents o in the hashtable,
     * e.g. returns o iff multiset.containsKey(o) else null
     */
    private TRSTerm getRep(final TRSTerm o) {
        if (this.multiset.get(o) != null) {
            return o;
        } else {
            return null;
        }
    }

    /** Returns the number of occurences of <code>o</code> in this multiset.
     */
    public int numberOfOccurences(final TRSTerm o) {
        final TRSTerm m = this.getRep(o);
        if (m != null) {
            return (this.multiset.get(m)).intValue();
        } else {
            return 0;
        }
    }

    /** Returns <code>true</code> iff <code>o</code> occurrs at least once in
     * this multiset, <code>false</code> otherwise.
     */
    public boolean contains(final TRSTerm o) {
        return this.getRep(o) != null;
    }

    /** Returns an <code>Enumeration</code> of the elements in this
     * multiset.
     * Each element occurs only once even if it is contained in
     * this multiset more than once.
     */
    public Enumeration<TRSTerm> elements() {
        return this.multiset.keys();
    }

    /** Returns a new <code>MultisetOfTerms</code> that is the union of this
     * multiset and the multiset <code>other</code>.
     */
    public MultisetOfTerms union(final MultisetOfTerms other) {
        final Vector<TRSTerm> multiVec = this.toRealTermVector();
        final Vector<TRSTerm> otherVec = other.toRealTermVector();

        for (final TRSTerm t : otherVec) {
            multiVec.add(t);
        }

        return MultisetOfTerms.create(multiVec);
    }

    /** Returns a new <code>MultisetOfTerms</code> that is the intersection of
     * this multiset and the multiset <code>other</code>.
     */
    public MultisetOfTerms intersect(final MultisetOfTerms other) {
        final Vector<TRSTerm> res = new Vector<TRSTerm>();
        int occ1, occ2;
        int occ;

        for (final TRSTerm t : other.toTermVector()) {
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

        return MultisetOfTerms.create(res);
    }

    /** Returns a new <code>MultisetOfTerms</code> that contains the elements
     * from this multiset that are not in the multiset <code>other</code>.
     */
    public MultisetOfTerms subtract(final MultisetOfTerms other) {
        final Vector<TRSTerm> res = new Vector<TRSTerm>();
        int occ;
        for (final TRSTerm t : this.toTermVector()) {
            occ = this.numberOfOccurences(t) - other.numberOfOccurences(t);
            for (int i = 0; i < occ; i++) {
                res.add(t);
            }
        }

        return MultisetOfTerms.create(res);
    }

    /** Returns a shallow copy of this multiset.
     */
    public MultisetOfTerms shallowcopy() {
        return MultisetOfTerms.create(this.toRealTermVector());
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

    /** Returns the number of elements in this multiset, taking their
     * multiplicity into account.
     */
    public int realSize() {
        return this.toRealTermVector().size();
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
    public Vector<TRSTerm> toTermVector() {
        final Vector<TRSTerm> res = new Vector<TRSTerm>();
        for (final TRSTerm t : this.multiset.keySet()) {
            res.add(t);
        }
        return res;
    }

    /** One copy of each entry, counting its
     * multiplicity.
     */
    public Vector<TRSTerm> toRealTermVector() {
        final Vector<TRSTerm> res = new Vector<TRSTerm>();
        for (final TRSTerm t : this.multiset.keySet()) {
            for (int i = 0; i < this.multiset.get(t); i++) {
                res.add(t);
            }
        }
        return res;
    }

}
