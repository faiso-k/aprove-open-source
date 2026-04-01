package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.*;

/**
 * A default implementation of ImmutableList<E>, provides all methods
 * from List<E> for arbitrary input lists. Useful for creating ImmutableLists
 * for lists for which no immutable class exists. Only downside: One cannot
 * access their methods which are not specified by List<E>.
 *
 * @author Carsten Fuhs
 * @version $Id$
 * @param <E> The type of the list's elements.
 */
class DefaultImmutableList<E> implements ImmutableList<E> {

    @Override
    public Stream<E> stream() {
        return this.list.stream();
    }

    @Override
    public Stream<E> parallelStream() {
        return this.list.parallelStream();
    }

    /**
     * @param <U> The type of the elements in the created list.
     * @param reference The List to be made immutable.
     * @return An immutable version of the specified List.
     */
    static <U> DefaultImmutableList<U> create(DefaultImmutableList<U> reference) {
        return reference;
    }

    /**
     * @param <U> The type of the elements in the created list.
     * @param reference The List to be made immutable.
     * @return An immutable version of the specified List.
     */
    static <U> DefaultImmutableList<U> create(List<U> reference) {
        return new DefaultImmutableList<U>(reference);
    }

    /**
     * Has hashValue already been computed?
     */
    private boolean hashValid;

    /**
     * Cache for the hash value of this.
     */
    private int hashValue;

    /**
     * Reference from the constructor, will not be modified by this class.
     */
    private final List<E> list;

    /**
     * @param ref The List to be made immutable.
     */
    private DefaultImmutableList(List<E> ref) {
        this.list = ref;
        this.hashValid = false;
    }

    /* (non-Javadoc)
     * @see java.util.List#add(java.lang.Object)
     */
    @Override
    public boolean add(E o) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    /* (non-Javadoc)
     * @see java.util.List#add(int, java.lang.Object)
     */
    @Override
    public void add(int index, E element) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    /* (non-Javadoc)
     * @see java.util.List#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends E> c) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    /* (non-Javadoc)
     * @see java.util.List#addAll(int, java.util.Collection)
     */
    @Override
    public boolean addAll(int index, Collection<? extends E> c) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    /* (non-Javadoc)
     * @see java.util.List#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    /* (non-Javadoc)
     * @see java.util.List#contains(java.lang.Object)
     */
    @Override
    public boolean contains (Object o) {
        return this.list.contains(o);
    }

    /* (non-Javadoc)
     * @see java.util.List#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return this.list.containsAll(c);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (! (o instanceof List)) {
            return false;
        }
        List<?> other = (List<?>) o;
        if (other.hashCode() != this.hashCode()) {
            return false;
        }
        return this.list.equals(other);
    }

    @Override
    public void forEach(Consumer<? super E> action)  {
        this.list.forEach(action);
    }

    /* (non-Javadoc)
     * @see java.util.List#get(int)
     */
    @Override
    public E get(int index) {
        return this.list.get(index);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        if (this.hashValid) {
            return this.hashValue;
        }
        else {
            this.hashValue = this.list.hashCode();
            this.hashValid = true;
            return this.hashValue;
        }
    }

    /* (non-Javadoc)
     * @see java.util.List#indexOf(java.lang.Object)
     */
    @Override
    public int indexOf(Object o) {
        return this.list.indexOf(o);
    }

    /* (non-Javadoc)
     * @see java.util.List#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.list.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.List#iterator()
     */
    @Override
    public Iterator<E> iterator() {
        return ImmutableIterator.create(this.list.iterator());
    }

    /* (non-Javadoc)
     * @see java.util.List#lastIndexOf(java.lang.Object)
     */
    @Override
    public int lastIndexOf(Object o) {
        return this.list.lastIndexOf(o);
    }

    /* (non-Javadoc)
     * @see java.util.List#listIterator()
     */
    @Override
    public ListIterator<E> listIterator() {
        return ImmutableListIterator.create(this.list.listIterator());
    }

    /* (non-Javadoc)
     * @see java.util.List#listIterator(int)
     */
    @Override
    public ListIterator<E> listIterator(int index) {
        return ImmutableListIterator.create(this.list.listIterator(index));
    }

    /* (non-Javadoc)
     * @see java.util.List#remove(int)
     */
    @Override
    public E remove(int index) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    /* (non-Javadoc)
     * @see java.util.List#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    /* (non-Javadoc)
     * @see java.util.List#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    /* (non-Javadoc)
     * @see java.util.List#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    /* (non-Javadoc)
     * @see java.util.List#set(int, java.lang.Object)
     */
    @Override
    public E set(int index, E element) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    /* (non-Javadoc)
     * @see java.util.List#size()
     */
    @Override
    public int size() {
        return this.list.size();
    }

    /* (non-Javadoc)
     * @see java.util.List#subList(int, int)
     */
    @Override
    public List<E> subList(int fromIndex, int toIndex) {
        return ImmutableCreator.create(this.list.subList(fromIndex, toIndex));
    }

    /* (non-Javadoc)
     * @see java.util.List#toArray()
     */
    @Override
    public Object[] toArray() {
        return this.list.toArray();
    }

    /* (non-Javadoc)
     * @see java.util.List#toArray(java.lang.Object[])
     */
    @Override
    public <T> T[] toArray(T[] a) {
        return this.list.toArray(a);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.list.toString();
    }

    @Override
    public void replaceAll(UnaryOperator<E> operator) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public void sort(Comparator<? super E> c) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public boolean removeIf(Predicate<? super E> filter) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public Spliterator<E> spliterator() {
        return this.list.spliterator();
    }

    @Override
    public <T> T[] toArray(IntFunction<T[]> generator) {
        return this.toArray(generator);
    }
}
