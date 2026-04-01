package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.stream.*;

/**
 * A default implementation of ImmutableDeque<E>, provides all methods from Deque<E> for arbitrary input deques. Useful
 * for creating ImmutableDeques for deques for which no immutable class exists. Only downside: One cannot access their
 * methods which are not specified by Deque<E>.
 * @author cryingshadow
 * @version $Id$
 * @param <E> The type of the deque's elements.
 */
class DefaultImmutableDeque<E> implements ImmutableDeque<E> {

    @Override
    public Stream<E> stream() {
        return this.deque.stream();
    }

    @Override
    public Stream<E> parallelStream() {
        return this.deque.parallelStream();
    }

    /**
     * @param <U> The type of the elements in the created deque.
     * @param reference The Deque to be made immutable.
     * @return An immutable version of the specified Deque.
     */
    static <U> DefaultImmutableDeque<U> create(DefaultImmutableDeque<U> reference) {
        return reference;
    }

    /**
     * @param <U> The type of the elements in the created deque.
     * @param reference The Deque to be made immutable.
     * @return An immutable version of the specified Deque.
     */
    static <U> DefaultImmutableDeque<U> create(Deque<U> reference) {
        return new DefaultImmutableDeque<U>(reference);
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
    private final Deque<E> deque;

    /**
     * @param ref The Deque to be made immutable.
     */
    private DefaultImmutableDeque(Deque<E> ref) {
        this.deque = ref;
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
     * @see java.util.List#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends E> c) {
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
        return this.deque.contains(o);
    }

    /* (non-Javadoc)
     * @see java.util.List#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return this.deque.containsAll(c);
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
        return this.deque.equals(other);
    }

    @Override
    public void forEach(Consumer<? super E> action)  {
        this.deque.forEach(action);
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
            this.hashValue = this.deque.hashCode();
            this.hashValid = true;
            return this.hashValue;
        }
    }

    /* (non-Javadoc)
     * @see java.util.List#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.deque.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.List#iterator()
     */
    @Override
    public Iterator<E> iterator() {
        return ImmutableIterator.create(this.deque.iterator());
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
     * @see java.util.List#size()
     */
    @Override
    public int size() {
        return this.deque.size();
    }

    /* (non-Javadoc)
     * @see java.util.List#toArray()
     */
    @Override
    public Object[] toArray() {
        return this.deque.toArray();
    }

    /* (non-Javadoc)
     * @see java.util.List#toArray(java.lang.Object[])
     */
    @Override
    public <T> T[] toArray(T[] a) {
        return this.deque.toArray(a);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.deque.toString();
    }

    @Override
    public void addFirst(E e) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public void addLast(E e) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public boolean offerFirst(E e) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public boolean offerLast(E e) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public E removeFirst() {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public E removeLast() {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public E pollFirst() {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public E pollLast() {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public E getFirst() {
        return this.deque.getFirst();
    }

    @Override
    public E getLast() {
        return this.deque.getLast();
    }

    @Override
    public E peekFirst() {
        return this.deque.peekFirst();
    }

    @Override
    public E peekLast() {
        return this.deque.peekLast();
    }

    @Override
    public boolean removeFirstOccurrence(Object o) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public boolean removeLastOccurrence(Object o) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public boolean offer(E e) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public E remove() {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public E poll() {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public E element() {
        return this.deque.element();
    }

    @Override
    public E peek() {
        return this.deque.peek();
    }

    @Override
    public void push(E e) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public E pop() {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public Iterator<E> descendingIterator() {
        return ImmutableIterator.create(this.deque.descendingIterator());
    }

    @Override
    public <T> T[] toArray(IntFunction<T[]> generator) {
        return this.deque.toArray(generator);
    }

    @Override
    public boolean removeIf(Predicate<? super E> filter) {
        throw new UnsupportedOperationException("changes not allowed in immutable lists!");
    }

    @Override
    public Spliterator<E> spliterator() {
        return this.deque.spliterator();
    }
}
