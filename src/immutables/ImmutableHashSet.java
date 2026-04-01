package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.stream.*;

/**
 * Class representing a HashSet which, once instantiated with a reference
 * HashSet, does not support any add, remove, clear or retain operation.
 * It wraps a mutable HashSet and relegates to this set's operations if
 * they do not change any contents of this set. Otherwise, an
 * UnsupportedOperationException is thrown, indicating that this operation
 * should not be used by the programmer.
 *
 * @author Peter Schneider-Kamp
 * @version $Id$
 * @param <E> The type of the set's elements.
 */
public class ImmutableHashSet<E> extends HashSet<E> implements ImmutableSet<E> {

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
    private static final long serialVersionUID = -4032452175834162322L;

    /**
     * @param <U> The type of the elements in the created set.
     * @param referenceSet The HashSet to be made immutable.
     * @return An immutable version of the specified HashSet.
     */
    static <U> ImmutableHashSet<U> create(HashSet<U> referenceSet) {
        return new ImmutableHashSet<U>(referenceSet);
    }

    /**
     * @param <U> The type of the elements in the created set.
     * @param referenceSet The HashSet to be made immutable.
     * @return An immutable version of the specified HashSet.
     */
    static <U> ImmutableHashSet<U> create(ImmutableHashSet<U> referenceSet) {
        return referenceSet;
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
    private final HashSet<E> set;

    /**
     * @param reference The HashSet to be made immutable.
     */
    private ImmutableHashSet(HashSet<E> reference) {
        super(0);
        this.set = reference;
        this.hashValid = false;
    }

    /* (non-Javadoc)
     * @see java.util.HashSet#add(java.lang.Object)
     */
    @Override
    public boolean add(E o) {
        throw new UnsupportedOperationException("Add operation is not allowed in ImmutableHashSets.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends E> c) {
        throw new UnsupportedOperationException("AddAll operation is not allowed in ImmutableHashSets.");
    }

    /* (non-Javadoc)
     * @see java.util.HashSet#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException("Clear operation is not allowed in ImmutableHashSets.");
    }

    /* (non-Javadoc)
     * @see java.util.HashSet#clone()
     */
    @Override
    public Object clone() {
        return this;
    }

    /* (non-Javadoc)
     * @see java.util.HashSet#contains(java.lang.Object)
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
     * @see java.util.HashSet#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.set.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.HashSet#iterator()
     */
    @Override
    public Iterator<E> iterator() {
        return ImmutableIterator.create(this.set.iterator());
    }

    /* (non-Javadoc)
     * @see java.util.HashSet#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableHashSets.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractSet#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException("Clear operation is not allowed in ImmutableHashSets.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException("RetainAll operation is not allowed in ImmutableHashSets.");
    }

    /* (non-Javadoc)
     * @see java.util.HashSet#size()
     */
    @Override
    public int size() {
        return this.set.size();
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
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableHashSets.");
    }

    @Override
    public Spliterator<E> spliterator() {
        return this.set.spliterator();
    }
}
