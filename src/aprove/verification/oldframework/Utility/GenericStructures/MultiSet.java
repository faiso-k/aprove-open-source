package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

/**
 *  A multiset is a mapping from elements to integers.
 *
 *  @author  Peter Schneider-Kamp, Stephan Falke
 *  @version $Id$
 */

public interface MultiSet<T> extends Map<T,Integer> {

    /**
     * Adds the element <code>e</code> to this multiset.
     * @return The number of elements added - here: 1.
     */
    public int add(T e);

    /**
     * Adds <code>occ</code> occurrences of the element <code>e</code> to
     * this multiset.
     * @param occ A positive integer.
     * @return The number of elements added - here: occ.
     */
    public int add(T e, int occ);

    /**
     * Removes one occurence of <code>e</code> from this multiset.
     * @return The number of elements removed.
     */
    public int removeOne(T e);

    /**
     * Removes <code>occ</code> occurences of <code>e</code> from this multiset.
     * @param occ A positive integer.
     * @return The number of elements removed.
     */
    public int remove(T e, int occ);

    /**
     * Removes all occurences of <code>e</code> from this multiset.
     */
    public int removeAny(T e);

    /**
     * Returns the number of occurences of <code>e</code> in this multiset.
     */
    public int frequency(T e);

    /**
     * Returns <code>true</code> if <code>e</code> occurrs at least once in
     * this multiset, <code>false</code> otherwise.
     */
    public boolean contains(T e);

    /** Returns <code>true</code> if this multiset is contained in the multiset
     * <code>other</code>, returns <code>false</code> otherwise.
     */
    public boolean containsAll(MultiSet<T> other);


    /**
     * Adds all elements in <code>other</code> to this multiset.
     */
    public void addAll(MultiSet<T> other);

    /**
     * Returns a new multiset that is the union of
     * this multiset and the multiset <code>other</code>.
     */
    public MultiSet<T> union(MultiSet<T> other);

    /**
     * Retains all elements in <code>other</code> in this.
     */
    public void retainAll(MultiSet<T> other);


    /**
     * Returns a new multiset that is the
     * intersection of this multiset and the multiset <code>other</code>.
     */
    public MultiSet<T> intersect(MultiSet<T> other);

    /**
     * Removes all elements occurring in <code>other</code> from this
     * multiset.
     */
    public void removeAll(MultiSet<T> other);

    /**
     * Returns a new multiset that contains the
     * elements from this multiset that are not in the multiset
     * <code>other</code>.
     */
    public MultiSet<T> subtract(MultiSet<T> other);

    /**
     * Returns a list containing the elements of
     * this multiset.
     */
    public List<T> toList();

    /**
     * Returns the cardinality of this multiset. Note that
     * <code>size</code> returns the cardinality of the set
     * that corresponds to this multiset.
     */
    public int multiSize();

    public boolean isSubsetOf(MultiSet<T> other);

}
