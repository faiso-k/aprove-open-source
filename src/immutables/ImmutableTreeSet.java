package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.stream.*;

/**
 * Class representing a TreeSet which, once instantiated with a reference TreeSet, does not support any operations
 * modifying the data structure. It wraps a mutable TreeSet and relegates to this set's operations if they do not
 * change any contents of this set. Otherwise, an UnsupportedOperationException is thrown, indicating that this
 * operation should not be used by the programmer.
 * @author cryingshadow
 * @version $Id$
 * @param <E> The type of the elements in this set.
 */
public class ImmutableTreeSet<E> extends TreeSet<E> implements ImmutableNavigableSet<E> {

    @Override
    public Stream<E> stream() {
        return this.set.stream();
    }

    @Override
    public Stream<E> parallelStream() {
        return this.set.parallelStream();
    }

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -1328271708366164983L;

    /**
     * @param <U> The type of the elements in the created set.
     * @param referenceSet The TreeSet to be made immutable.
     * @return An immutable version of the specified TreeSet.
     */
    static <U> ImmutableTreeSet<U> create(ImmutableTreeSet<U> referenceSet) {
        return referenceSet;
    }

    /**
     * @param <U> The type of the elements in the created set.
     * @param referenceSet The TreeSet to be made immutable.
     * @return An immutable version of the specified TreeSet.
     */
    static <U> ImmutableTreeSet<U> create(TreeSet<U> referenceSet) {
        return new ImmutableTreeSet<U>(referenceSet);
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
     * Reference from the constructor.
     */
    private final TreeSet<E> set;

    /**
     * @param reference The TreeSet to be made immutable.
     */
    private ImmutableTreeSet(TreeSet<E> reference) {
        super();
        this.set = reference;
        this.hashValid = false;
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#add(java.lang.Object)
     */
    @Override
    public boolean add(E o) {
        throw new UnsupportedOperationException("Add operation is not allowed in ImmutableTreeSets.");
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends E> c) {
        throw new UnsupportedOperationException("AddAll operation is not allowed in ImmutableTreeSets.");
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#ceiling(java.lang.Object)
     */
    @Override
    public E ceiling(E e) {
        return this.set.ceiling(e);
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException("Clear operation is not allowed in ImmutableTreeSets.");
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#clone()
     */
    @Override
    public Object clone() {
        return this;
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#comparator()
     */
    @Override
    public Comparator<? super E> comparator() {
        return this.set.comparator();
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#contains(java.lang.Object)
     */
    @Override
    public boolean contains(Object o) {
        return this.set.contains(o);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return this.set.containsAll(c);
    }


    /* (non-Javadoc)
     * @see java.util.TreeSet#descendingIterator()
     */
    @Override
    public Iterator<E> descendingIterator() {
        return ImmutableIterator.create(this.set.descendingIterator());
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#descendingSet()
     */
    @Override
    public NavigableSet<E> descendingSet() {
        return ImmutableCreator.create(this.set.descendingSet());
    }

    /* (non-Javadoc)
     * @see java.util.AbstractSet#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (! (o instanceof Set)) {
            return false;
        }
        Set<?> other = (Set<?>) o;
        if (other.hashCode() != this.hashCode()) {
            return false;
        }
        return this.set.equals(other);
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#first()
     */
    @Override
    public E first() {
        return this.set.first();
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#floor(java.lang.Object)
     */
    @Override
    public E floor(E e) {
        return this.set.floor(e);
    }

    @Override
    public void forEach(Consumer<? super E> action)  {
        this.set.forEach(action);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractSet#hashCode()
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
     * @see java.util.TreeSet#headSet(java.lang.Object)
     */
    @Override
    public SortedSet<E> headSet(E toElement) {
        return ImmutableCreator.create(this.set.headSet(toElement));
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#headSet(java.lang.Object, boolean)
     */
    @Override
    public NavigableSet<E> headSet(E toElement, boolean inclusive) {
        return ImmutableCreator.create(this.set.headSet(toElement, inclusive));
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#higher(java.lang.Object)
     */
    @Override
    public E higher(E e) {
        return this.set.higher(e);
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.set.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#iterator()
     */
    @Override
    public Iterator<E> iterator() {
        return ImmutableIterator.create(this.set.iterator());
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#last()
     */
    @Override
    public E last() {
        return this.set.last();
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#lower(java.lang.Object)
     */
    @Override
    public E lower(E e) {
        return this.set.lower(e);
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#pollFirst()
     */
    @Override
    public E pollFirst() {
        throw new UnsupportedOperationException("PollFirst operation is not allowed in ImmutableTreeSets.");
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#pollLast()
     */
    @Override
    public E pollLast() {
        throw new UnsupportedOperationException("PollLast operation is not allowed in ImmutableTreeSets.");
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableTreeSets.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractSet#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException("RemoveAll operation is not allowed in ImmutableTreeSets.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException("RetainAll operation is not allowed in ImmutableTreeSets.");
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#size()
     */
    @Override
    public int size() {
        return this.set.size();
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#subSet(java.lang.Object, boolean, java.lang.Object, boolean)
     */
    @Override
    public NavigableSet<E> subSet(E fromElement, boolean fromInclusive, E toElement, boolean toInclusive) {
        return ImmutableCreator.create(this.set.subSet(fromElement, fromInclusive, toElement, toInclusive));
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#subSet(java.lang.Object, java.lang.Object)
     */
    @Override
    public SortedSet<E> subSet(E fromElement, E toElement) {
        return ImmutableCreator.create(this.set.subSet(fromElement, toElement));
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#tailSet(java.lang.Object)
     */
    @Override
    public SortedSet<E> tailSet(E fromElement) {
        return ImmutableCreator.create(this.set.tailSet(fromElement));
    }

    /* (non-Javadoc)
     * @see java.util.TreeSet#tailSet(java.lang.Object, boolean)
     */
    @Override
    public NavigableSet<E> tailSet(E fromElement, boolean inclusive) {
        return ImmutableCreator.create(this.set.tailSet(fromElement, inclusive));
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#toArray()
     */
    @Override
    public Object[] toArray() {
        return this.set.toArray();
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#toArray(java.lang.Object[])
     */
    @Override
    public <T> T[] toArray(T[] a) {
        return this.set.toArray(a);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#toString()
     */
    @Override
    public String toString() {
        return this.set.toString();
    }

    @Override
    public <T> T[] toArray(IntFunction<T[]> generator) {
        return this.set.toArray(generator);
    }

    @Override
    public boolean removeIf(Predicate<? super E> filter) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableTreeSets.");
    }

    @Override
    public Spliterator<E> spliterator() {
        return this.set.spliterator();
    }

}
