package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.stream.*;

/**
 * Default implementation for immutable sorted sets. Useful for creating immutable sorted sets for sets which do
 * not have an immutable class of their own. However, you can only use the (non-destructive) methods which are
 * specified by SortedSet<E>.
 * @author cryingshadow
 * @version $Id$
 * @param <E> The type of elements in this set.
 */
class DefaultImmutableSortedSet<E> implements ImmutableSortedSet<E> {

    @Override
    public Stream<E> stream() {
        return this.set.stream();
    }

    @Override
    public Stream<E> parallelStream() {
        return this.set.parallelStream();
    }

    /**
     * @param <U> The type of the elements in the created set.
     * @param referenceSet The SortedSet to be made immutable.
     * @return An immutable version of the specified SortedSet.
     */
    static <U> DefaultImmutableSortedSet<U> create(DefaultImmutableSortedSet<U> referenceSet) {
        return referenceSet;
    }

    /**
     * @param <U> The type of the elements in the created set.
     * @param referenceSet The SortedSet to be made immutable.
     * @return An immutable version of the specified SortedSet.
     */
    static <U> DefaultImmutableSortedSet<U> create(SortedSet<U> referenceSet) {
        return new DefaultImmutableSortedSet<U>(referenceSet);
    }

    /**
     * Has the hash value already been computed?
     */
    private boolean hashValid;

    /**
     * Cache for the hash value.
     */
    private int hashValue;

    /**
     * Constructor reference.
     */
    private final SortedSet<E> set;

    /**
     * @param reference SortedSet to be made immutable.
     */
    private DefaultImmutableSortedSet(SortedSet<E> reference) {
        this.set = reference;
        this.hashValid = false;
    }

    /* (non-Javadoc)
     * @see java.util.Set#add(java.lang.Object)
     */
    @Override
    public boolean add(E o) {
        throw new UnsupportedOperationException("Add operation is not allowed in immutable sets.");
    }

    /* (non-Javadoc)
     * @see java.util.Set#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends E> c) {
        throw new UnsupportedOperationException("AddAll operation is not allowed in immutable sets.");
    }

    /* (non-Javadoc)
     * @see java.util.Set#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException("Clear operation is not allowed in immutable sets.");
    }

    /* (non-Javadoc)
     * @see java.lang.Object#clone()
     */
    @Override
    public Object clone() {
        return this;
    }

    /* (non-Javadoc)
     * @see java.util.SortedSet#comparator()
     */
    @Override
    public Comparator<? super E> comparator() {
        return this.set.comparator();
    }

    /* (non-Javadoc)
     * @see java.util.Set#contains(java.lang.Object)
     */
    @Override
    public boolean contains(Object o) {
        return this.set.contains(o);
    }

    /* (non-Javadoc)
     * @see java.util.Set#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return this.set.containsAll(c);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (! (o instanceof NavigableSet)) {
            return false;
        }
        NavigableSet<?> other = (NavigableSet<?>) o;
        if (other.hashCode() != this.hashCode()) {
            return false;
        }
        return this.set.equals(other);
    }

    @Override
    public void forEach(Consumer<? super E> action)  {
        this.set.forEach(action);
    }

    /* (non-Javadoc)
     * @see java.util.SortedSet#first()
     */
    @Override
    public E first() {
        return this.set.first();
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
            this.hashValue = this.set.hashCode();
            this.hashValid = true;
            return this.hashValue;
        }
    }

    /* (non-Javadoc)
     * @see java.util.NavigableSet#headSet(java.lang.Object)
     */
    @Override
    public SortedSet<E> headSet(E toElement) {
        return ImmutableCreator.create(this.set.headSet(toElement));
    }

    /* (non-Javadoc)
     * @see java.util.Set#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.set.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.NavigableSet#iterator()
     */
    @Override
    public Iterator<E> iterator() {
        return ImmutableIterator.create(this.set.iterator());
    }

    /* (non-Javadoc)
     * @see java.util.SortedSet#last()
     */
    @Override
    public E last() {
        return this.set.last();
    }

    /* (non-Javadoc)
     * @see java.util.Set#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException("Remove operation is not allowed in immutable sets.");
    }

    /* (non-Javadoc)
     * @see java.util.Set#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException("RemoveAll operation is not allowed in immutable sets.");
    }

    /* (non-Javadoc)
     * @see java.util.Set#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException("RetainAll operation is not allowed in immutable sets.");
    }

    /* (non-Javadoc)
     * @see java.util.Set#size()
     */
    @Override
    public int size() {
        return this.set.size();
    }

    /* (non-Javadoc)
     * @see java.util.NavigableSet#subSet(java.lang.Object, java.lang.Object)
     */
    @Override
    public SortedSet<E> subSet(E fromElement, E toElement) {
        return ImmutableCreator.create(this.set.subSet(fromElement, toElement));
    }

    /* (non-Javadoc)
     * @see java.util.NavigableSet#tailSet(java.lang.Object)
     */
    @Override
    public SortedSet<E> tailSet(E fromElement) {
        return ImmutableCreator.create(this.set.tailSet(fromElement));
    }

    /* (non-Javadoc)
     * @see java.util.Set#toArray()
     */
    @Override
    public Object[] toArray() {
        return this.set.toArray();
    }

    /* (non-Javadoc)
     * @see java.util.Set#toArray(java.lang.Object[])
     */
    @Override
    public <T> T[] toArray(T[] a) {
        return this.set.toArray(a);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.set.toString();
    }

    @Override
    public Spliterator<E> spliterator() {
        return this.set.spliterator();
    }

    @Override
    public <T> T[] toArray(IntFunction<T[]> generator) {
        return this.set.toArray(generator);
    }

    @Override
    public boolean removeIf(Predicate<? super E> filter) {
        throw new UnsupportedOperationException("Modifications are not allowed in immutable sets.");
    }
}
