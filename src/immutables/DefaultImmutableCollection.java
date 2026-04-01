package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.stream.*;

/**
 * A default implementation of ImmutableCollection<E>, provides all methods
 * from Collection<E> for arbitrary input collections. Useful for creating
 * ImmutableCollections for collections for which no immutable class exists.
 * You can only use methods which are specified by Collection.
 *
 * @author Carsten Fuhs
 * @version $Id$
 * @param <E> The type of the collection's elements.
 */
class DefaultImmutableCollection<E> implements ImmutableCollection<E> {

    @Override
    public Stream<E> stream() {
        return this.collection.stream();
    }

    @Override
    public Stream<E> parallelStream() {
        return this.collection.parallelStream();
    }

    /**
     * @param <U> The type of the elements in the created collection.
     * @param reference The Collection to be made immutable.
     * @return An immutable version of the specified Collection.
     */
    static <U> DefaultImmutableCollection<U> create(Collection<U> reference) {
        return new DefaultImmutableCollection<U>(reference);
    }

    /**
     * @param <U> The type of the elements in the created collection.
     * @param reference The Collection to be made immutable.
     * @return An immutable version of the specified Collection.
     */
    static <U> DefaultImmutableCollection<U> create(DefaultImmutableCollection<U> reference) {
        return reference;
    }

    /**
     * Constructor reference.
     */
    private final Collection<E> collection;

    /**
     * Has the hash been computed already?
     */
    private boolean hashValid;

    /**
     * Cache for hash.
     */
    private int hashValue;

    /**
     * @param ref Collection to be made immutable.
     */
    private DefaultImmutableCollection(Collection<E> ref) {
        this.collection = ref;
        this.hashValid = false;
    }

    /* (non-Javadoc)
     * @see java.util.Collection#add(java.lang.Object)
     */
    @Override
    public boolean add(E o) {
        throw new UnsupportedOperationException("changes not allowed in immutable collections!");
    }

    /* (non-Javadoc)
     * @see java.util.Collection#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends E> c) {
        throw new UnsupportedOperationException("changes not allowed in immutable collections!");
    }

    /* (non-Javadoc)
     * @see java.util.Collection#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException("changes not allowed in immutable collections!");
    }

    /* (non-Javadoc)
     * @see java.util.Collection#contains(java.lang.Object)
     */
    @Override
    public boolean contains (Object o) {
        return this.collection.contains(o);
    }

    /* (non-Javadoc)
     * @see java.util.Collection#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return this.collection.containsAll(c);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (! (o instanceof Collection)) {
            return false;
        }
        Collection<?> other = (Collection<?>) o;
        if (other.hashCode() != this.hashCode()) {
            return false;
        }
        return this.collection.equals(other);
    }

    @Override
    public void forEach(Consumer<? super E> action)  {
        this.collection.forEach(action);
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
            this.hashValue = this.collection.hashCode();
            this.hashValid = true;
            return this.hashValue;
        }
    }

    /* (non-Javadoc)
     * @see java.util.Collection#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.collection.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.Collection#iterator()
     */
    @Override
    public Iterator<E> iterator() {
        return ImmutableIterator.create(this.collection.iterator());
    }

    /* (non-Javadoc)
     * @see java.util.Collection#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException("changes not allowed in immutable collections!");
    }

    /* (non-Javadoc)
     * @see java.util.Collection#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException("changes not allowed in immutable collections!");
    }

    /* (non-Javadoc)
     * @see java.util.Collection#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException("changes not allowed in immutable collections!");
    }

    /* (non-Javadoc)
     * @see java.util.Collection#size()
     */
    @Override
    public int size() {
        return this.collection.size();
    }

    /* (non-Javadoc)
     * @see java.util.Collection#toArray()
     */
    @Override
    public Object[] toArray() {
        return this.collection.toArray();
    }

    /* (non-Javadoc)
     * @see java.util.Collection#toArray(java.lang.Object[])
     */
    @Override
    public <T> T[] toArray(T[] a) {
        return this.collection.toArray(a);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.collection.toString();
    }

    @Override
    public <T> T[] toArray(IntFunction<T[]> generator) {
        return this.collection.toArray(generator);
    }

    @Override
    public boolean removeIf(Predicate<? super E> filter) {
        throw new UnsupportedOperationException("changes not allowed in immutable collections!");
    }

    @Override
    public Spliterator<E> spliterator() {
        return this.collection.spliterator();
    }
}



