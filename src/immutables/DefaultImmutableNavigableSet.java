package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.stream.*;

/**
 * Default implementation for immutable navigable sets, useful for creating immutable navigable sets for sets which do
 * not have an immutable class of their own. However, you can only use the (non-destructive) methods which are
 * specified by NavigableSet<E>.
 * @author cryingshadow
 * @version $Id$
 */
class DefaultImmutableNavigableSet<E> implements ImmutableNavigableSet<E> {

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
     * @param referenceSet The NavigableSet to be made immutable.
     * @return An immutable version of the specified NavigableSet.
     */
    static <U> DefaultImmutableNavigableSet<U> create(DefaultImmutableNavigableSet<U> referenceSet) {
        return referenceSet;
    }

    /**
     * @param <U> The type of the elements in the created set.
     * @param referenceSet The NavigableSet to be made immutable.
     * @return An immutable version of the specified NavigableSet.
     */
    static <U> DefaultImmutableNavigableSet<U> create(NavigableSet<U> referenceSet) {
        return new DefaultImmutableNavigableSet<U>(referenceSet);
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
    private final NavigableSet<E> set;

    /**
     * @param reference NavigableSet to be made immutable.
     */
    private DefaultImmutableNavigableSet(NavigableSet<E> reference) {
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
     * @see java.util.NavigableSet#ceiling(java.lang.Object)
     */
    @Override
    public E ceiling(E e) {
        return this.set.ceiling(e);
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
     * @see java.util.NavigableSet#descendingIterator()
     */
    @Override
    public Iterator<E> descendingIterator() {
        return ImmutableIterator.create(this.set.descendingIterator());
    }

    /* (non-Javadoc)
     * @see java.util.NavigableSet#descendingSet()
     */
    @Override
    public NavigableSet<E> descendingSet() {
        return ImmutableCreator.create(this.set.descendingSet());
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
     * @see java.util.NavigableSet#floor(java.lang.Object)
     */
    @Override
    public E floor(E e) {
        return this.set.floor(e);
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
     * @see java.util.NavigableSet#headSet(java.lang.Object, boolean)
     */
    @Override
    public NavigableSet<E> headSet(E toElement, boolean inclusive) {
        return ImmutableCreator.create(this.set.headSet(toElement, inclusive));
    }

    /* (non-Javadoc)
     * @see java.util.NavigableSet#higher(java.lang.Object)
     */
    @Override
    public E higher(E e) {
        return this.set.higher(e);
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
     * @see java.util.NavigableSet#lower(java.lang.Object)
     */
    @Override
    public E lower(E e) {
        return this.set.lower(e);
    }

    /* (non-Javadoc)
     * @see java.util.NavigableSet#pollFirst()
     */
    @Override
    public E pollFirst() {
        throw new UnsupportedOperationException("PollFirst operation is not allowed in immutable sets.");
    }

    /* (non-Javadoc)
     * @see java.util.NavigableSet#pollLast()
     */
    @Override
    public E pollLast() {
        throw new UnsupportedOperationException("PollLast operation is not allowed in immutable sets.");
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
     * @see java.util.NavigableSet#subSet(java.lang.Object, boolean, java.lang.Object, boolean)
     */
    @Override
    public NavigableSet<E> subSet(E fromElement, boolean fromInclusive, E toElement, boolean toInclusive) {
        return ImmutableCreator.create(this.set.subSet(fromElement, fromInclusive, toElement, toInclusive));
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
     * @see java.util.NavigableSet#tailSet(java.lang.Object, boolean)
     */
    @Override
    public NavigableSet<E> tailSet(E fromElement, boolean inclusive) {
        return ImmutableCreator.create(this.set.tailSet(fromElement, inclusive));
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
