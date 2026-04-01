package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

/**
 * A set implementation offering random access by an index. The indices of the elements correspond to the insertion
 * order of the elements.
 * @author cryingshadow
 * @version $Id$
 * @param <E> The type of the elements.
 */
public class RandomAccessSet<E> extends AbstractSet<E> {

    /**
     * A list containing the same elements, but allowing random access.
     */
    private final List<E> list;

    /**
     * The backing set for this random access set.
     */
    private final Set<E> set;

    /**
     * Creates an empty random access set.
     */
    public RandomAccessSet() {
        this.set = new LinkedHashSet<E>();
        this.list = new ArrayList<E>();
    }

    /**
     * Creates a random access set with the elements in the specified collection. Equivalent to creating an empty
     * random access set and then adding all elements in the specified collection.
     * @param c Some collection of elements.
     */
    public RandomAccessSet(Collection<? extends E> c) {
        this();
        this.addAll(c);
    }

    @Override
    public boolean add(E elem) {
        if (this.set.add(elem)) {
            return this.list.add(elem);
        }
        return false;
    }

    /**
     * Inserts the specified element at the specified position in this set if it is not present already. Shifts the
     * element currently at that position (if any) and any subsequent elements to the right (adds one to their indices).
     * @param index The index at which the specified element is to be inserted.
     * @param elem The element to be inserted.
     * @return True if this set did not already contain the specified element. False otherwise.
     */
    public boolean add(int index, E elem) {
        if (this.set.add(elem)) {
            this.list.add(index, elem);
            return true;
        }
        return false;
    }

    /**
     * @param index The index of an element.
     * @return The element at the specified index.
     */
    public E get(int index) {
        return this.list.get(index);
    }

    @Override
    public Iterator<E> iterator() {
        final Iterator<E> setIt = this.set.iterator();
        final Iterator<E> listIt = this.list.iterator();
        return
            new Iterator<E>() {

                @Override
                public boolean hasNext() {
                    return listIt.hasNext();
                }

                @Override
                public E next() {
                    setIt.next();
                    return listIt.next();
                }

                @Override
                public void remove() {
                    setIt.remove();
                    listIt.remove();
                }

            };
    }

    /**
     * Removes the element at the specified index (reduced the indices of elements with a higher index by one).
     * @param index The index of the element to remove.
     * @return The removed element.
     */
    public E remove(int index) {
        E res = this.list.remove(index);
        this.set.remove(res);
        return res;
    }

    @Override
    public int size() {
        return this.set.size();
    }

}
