package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.stream.*;

/**
 * Class representing an ArrayDeque which, once instantiated with a reference
 * ArrayDeque, does not support any operations which would change the state
 * of this ArrayDeque.<p>
 * It wraps a mutable ArrayDeque and relegates to this ArrayDeque's operations if
 * they do not change any contents of this ArrayDeque. Otherwise, an
 * UnsupportedOperationException is thrown, indicating that this operation
 * should not be used by the programmer.
 * @author cryingshadow
 * @version $Id$
 * @param <A> Type of elements.
 */
public final class ImmutableArrayDeque<A> extends ArrayDeque<A> implements ImmutableDeque<A> {

    @Override
    public Stream<A> stream() {
        return this.arrayDeque.stream();
    }

    @Override
    public Stream<A> parallelStream() {
        return this.arrayDeque.parallelStream();
    }

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -3560247831777414451L;

    /**
     * @param <U> The generic type of the (Immutable)ArrayDeque.
     * @param referenceArrayDeque The ArrayDeque to make immutable.
     * @return An immutable version of the specified ArrayDeque.
     */
    static <U> ImmutableArrayDeque<U> create(ArrayDeque<U> referenceArrayDeque) {
        return new ImmutableArrayDeque<U>(referenceArrayDeque);
    }

    /**
     * @param <U> The generic type of the ImmutableArrayDeque.
     * @param referenceArrayDeque The ArrayDeque to make immutable.
     * @return An immutable version of the specified ArrayDeque.
     */
    static <U> ImmutableArrayDeque<U> create(ImmutableArrayDeque<U> referenceArrayDeque) {
        return referenceArrayDeque;
    }

    /**
     * Reference from the constructor, will not be modified by this class.
     */
    private final ArrayDeque<A> arrayDeque;

    /**
     * Has hashValue already been computed?
     */
    private boolean hashValid;

    /**
     * Cache for the hash value of this.
     */
    private int hashValue;

    /**
     * Wraps the specified ArrayDeque and initializes hashValid to false.
     * @param reference The ArrayDeque to make immutable.
     */
    private ImmutableArrayDeque(ArrayDeque<A> reference) {
        super(0);
        this.arrayDeque = reference;
        this.hashValid = false;
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#add(java.lang.Object)
     */
    @Override
    public boolean add(A o) {
        throw new UnsupportedOperationException("Add operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends A> collection) {
        throw new UnsupportedOperationException("AddAll operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#addFirst(java.lang.Object)
     */
    @Override
    public void addFirst(A e) {
        throw new UnsupportedOperationException("AddFirst operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#addLast(java.lang.Object)
     */
    @Override
    public void addLast(A e) {
        throw new UnsupportedOperationException("AddLast operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException("Clear operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#clone()
     */
    @Override
    public ArrayDeque<A> clone() {
        return this;
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#contains(java.lang.Object)
     */
    @Override
    public boolean contains(Object object) {
        return this.arrayDeque.contains(object);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return this.arrayDeque.containsAll(c);
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#descendingIterator()
     */
    @Override
    public Iterator<A> descendingIterator() {
        return ImmutableIterator.create(this.arrayDeque.descendingIterator());
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#element()
     */
    @Override
    public A element() {
        return this.arrayDeque.element();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (! (o instanceof Deque)) {
            return false;
        }
        Deque<?> other = (Deque<?>) o;
        if (other.hashCode() != this.hashCode()) {
            return false;
        }
        return this.arrayDeque.equals(other);
    }

    @Override
    public void forEach(Consumer<? super A> action)  {
        this.arrayDeque.forEach(action);
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#getFirst()
     */
    @Override
    public A getFirst() {
        return this.arrayDeque.getFirst();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#getLast()
     */
    @Override
    public A getLast() {
        return this.arrayDeque.getLast();
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
            this.hashValue = this.arrayDeque.hashCode();
            this.hashValid = true;
            return this.hashValue;
        }
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.arrayDeque.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#iterator()
     */
    @Override
    public Iterator<A> iterator() {
        return ImmutableIterator.create(this.arrayDeque.iterator());
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#offer(java.lang.Object)
     */
    @Override
    public boolean offer(A e) {
        throw new UnsupportedOperationException("Offer operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#offerFirst(java.lang.Object)
     */
    @Override
    public boolean offerFirst(A e) {
        throw new UnsupportedOperationException("OfferFirst operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#offerLast(java.lang.Object)
     */
    @Override
    public boolean offerLast(A e) {
        throw new UnsupportedOperationException("OfferLast operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#peek()
     */
    @Override
    public A peek() {
        return this.arrayDeque.peek();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#peekFirst()
     */
    @Override
    public A peekFirst() {
        return this.arrayDeque.peekFirst();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#peekLast()
     */
    @Override
    public A peekLast() {
        return this.arrayDeque.peekLast();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#poll()
     */
    @Override
    public A poll() {
        throw new UnsupportedOperationException("Poll operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#pollFirst()
     */
    @Override
    public A pollFirst() {
        throw new UnsupportedOperationException("PollFirst operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#pollLast()
     */
    @Override
    public A pollLast() {
        throw new UnsupportedOperationException("PollLast operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#pop()
     */
    @Override
    public A pop() {
        throw new UnsupportedOperationException("Pop operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#push(java.lang.Object)
     */
    @Override
    public void push(A e) {
        throw new UnsupportedOperationException("Push operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#remove()
     */
    @Override
    public A remove() {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> collection) {
        throw new UnsupportedOperationException("RemoveAll operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#removeFirst()
     */
    @Override
    public A removeFirst() {
        throw new UnsupportedOperationException("RemoveFirst operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#removeFirstOccurrence(java.lang.Object)
     */
    @Override
    public boolean removeFirstOccurrence(Object o) {
        throw new UnsupportedOperationException("RemoveFirstOccurrence operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#removeLast()
     */
    @Override
    public A removeLast() {
        throw new UnsupportedOperationException("RemoveLast operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#removeLastOccurrence(java.lang.Object)
     */
    @Override
    public boolean removeLastOccurrence(Object o) {
        throw new UnsupportedOperationException("RemoveLastOccurrence operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> collection) {
        throw new UnsupportedOperationException("RetainAll operation is not allowed in ImmutableArrayDeques.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#size()
     */
    @Override
    public int size() {
        return this.arrayDeque.size();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#toArray()
     */
    @Override
    public Object[] toArray() {
        return this.arrayDeque.toArray();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayDeque#toArray(java.lang.Object[])
     */
    @Override
    public <B> B[] toArray(B[] a) {
        return this.arrayDeque.toArray(a);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#toString()
     */
    @Override
    public String toString() {
        return this.arrayDeque.toString();
    }

    @Override
    public <T> T[] toArray(IntFunction<T[]> generator) {
        return this.arrayDeque.toArray(generator);
    }

    @Override
    public Spliterator<A> spliterator() {
        return this.arrayDeque.spliterator();
    }

    @Override
    public boolean removeIf(Predicate<? super A> filter) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableArrayDeques.");
    }
}
