package immutables;

import java.util.*;

/**
 * Class representing an iterator which does not support a remove operation.
 * It is used as a wrapper around a mutable iterator, but catching it's remove
 * operation and throwing an exception.
 * 
 * @author Peter Schneider-Kamp, cryingshadow
 * @version $Id$
 * @param <T> The type of the elements to be iterated over.
 */
public class ImmutableListIterator<T> extends ImmutableIterator<T> implements ListIterator<T> {
    
    /**
     * @param <U> The type of the elements to be iterated over.
     * @param reference The ListIterator to be made immutable.
     * @return An immutable version of the specified ListIterator.
     */
    static <U> ImmutableListIterator<U> create(ImmutableListIterator<U> reference) {
        return reference;
    }

    /**
     * @param <U> The type of the elements to be iterated over.
     * @param reference The ListIterator to be made immutable.
     * @return An immutable version of the specified ListIterator.
     */
    static <U> ImmutableListIterator<U> create(ListIterator<U> reference) {
        return new ImmutableListIterator<U>(reference);
    }
    
    /**
     * @param iterator The ListIterator reference.
     */
    private ImmutableListIterator(ListIterator<T> iterator) {
        super(iterator);
    }

    /* (non-Javadoc)
     * @see java.util.ListIterator#add(java.lang.Object)
     */
    @Override
    public void add(T o) {
        throw new UnsupportedOperationException("Add operation is not allowed in immutable list iterators.");
    }

    /* (non-Javadoc)
     * @see java.util.ListIterator#hasPrevious()
     */
    @Override
    public boolean hasPrevious() {
        return ((ListIterator<T>)this.iterator).hasPrevious();
    }

    /* (non-Javadoc)
     * @see java.util.ListIterator#nextIndex()
     */
    @Override
    public int nextIndex() {
        return ((ListIterator<T>)this.iterator).nextIndex();
    }

    /* (non-Javadoc)
     * @see java.util.ListIterator#previous()
     */
    @Override
    public T previous() {
        return ((ListIterator<T>)this.iterator).previous();
    }

    /* (non-Javadoc)
     * @see java.util.ListIterator#previousIndex()
     */
    @Override
    public int previousIndex() {
        return ((ListIterator<T>)this.iterator).previousIndex();
    }

    /* (non-Javadoc)
     * @see java.util.ListIterator#set(java.lang.Object)
     */
    @Override
    public void set(T o) {
        throw new UnsupportedOperationException("Set operation is not allowed in immutable list iterators.");
    }

}
