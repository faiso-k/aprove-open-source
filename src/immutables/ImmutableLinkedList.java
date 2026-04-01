package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.*;

/**
 * Class representing an LinkedList which, once instantiated with a reference
 * LinkedList, does not support any operations which would change the state
 * of this LinkedList.<p>
 * It wraps a mutable LinkedList and relegates to this LinkedList's operations if
 * they do not change any contents of this LinkedList. Otherwise, an
 * UnsupportedOperationException is thrown, indicating that this operation
 * should not be used by the programmer.
 * @author cryingshadow
 * @version $Id$
 * @param <E> Type of elements.
 */
public final class ImmutableLinkedList<E> extends LinkedList<E> implements ImmutableDeque<E>, ImmutableList<E> {

    @Override
    public Stream<E> stream() {
        return this.linkedList.stream();
    }

    @Override
    public Stream<E> parallelStream() {
        return this.linkedList.parallelStream();
    }

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -3560247831777414451L;

    /**
     * @param <U> The generic type of the ImmutableLinkedList.
     * @param referenceLinkedList The LinkedList to make immutable.
     * @return An immutable version of the specified LinkedList.
     */
    static <U> ImmutableLinkedList<U> create(ImmutableLinkedList<U> referenceLinkedList) {
        return referenceLinkedList;
    }

    /**
     * @param <U> The generic type of the (Immutable)LinkedList.
     * @param referenceLinkedList The LinkedList to make immutable.
     * @return An immutable version of the specified LinkedList.
     */
    static <U> ImmutableLinkedList<U> create(LinkedList<U> referenceLinkedList) {
        return new ImmutableLinkedList<U>(referenceLinkedList);
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
    private final LinkedList<E> linkedList;

    /**
     * Wraps the specified LinkedList and initializes hashValid to false.
     * @param reference The LinkedList to make immutable.
     */
    private ImmutableLinkedList(LinkedList<E> reference) {
        this.linkedList = reference;
        this.hashValid = false;
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#add(java.lang.Object)
     */
    @Override
    public boolean add(E o) {
        throw new UnsupportedOperationException("Add operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends E> collection) {
        throw new UnsupportedOperationException("AddAll operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#addAll(int, java.util.Collection)
     */
    @Override
    public boolean addAll(int index, Collection<? extends E> c) {
        throw new UnsupportedOperationException("AddAll operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#addFirst(java.lang.Object)
     */
    @Override
    public void addFirst(E e) {
        throw new UnsupportedOperationException("AddFirst operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#addLast(java.lang.Object)
     */
    @Override
    public void addLast(E e) {
        throw new UnsupportedOperationException("AddLast operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException("Clear operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#clone()
     */
    @Override
    public LinkedList<E> clone() {
        return this;
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#contains(java.lang.Object)
     */
    @Override
    public boolean contains(Object object) {
        return this.linkedList.contains(object);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return this.linkedList.containsAll(c);
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#descendingIterator()
     */
    @Override
    public Iterator<E> descendingIterator() {
        return ImmutableIterator.create(this.linkedList.descendingIterator());
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#element()
     */
    @Override
    public E element() {
        return this.linkedList.element();
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
        return this.linkedList.equals(other);
    }

    @Override
    public void forEach(Consumer<? super E> action)  {
        this.linkedList.forEach(action);
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#get(int)
     */
    @Override
    public E get(int index) {
        return this.linkedList.get(index);
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#getFirst()
     */
    @Override
    public E getFirst() {
        return this.linkedList.getFirst();
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#getLast()
     */
    @Override
    public E getLast() {
        return this.linkedList.getLast();
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
            this.hashValue = this.linkedList.hashCode();
            this.hashValid = true;
            return this.hashValue;
        }
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#indexOf(java.lang.Object)
     */
    @Override
    public int indexOf(Object o) {
        return this.linkedList.indexOf(o);
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.linkedList.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#iterator()
     */
    @Override
    public Iterator<E> iterator() {
        return ImmutableIterator.create(this.linkedList.iterator());
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#lastIndexOf(java.lang.Object)
     */
    @Override
    public int lastIndexOf(Object o) {
        return this.linkedList.lastIndexOf(o);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractList#listIterator()
     */
    @Override
    public ListIterator<E> listIterator() {
        return ImmutableListIterator.create(this.linkedList.listIterator());
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#listIterator(int)
     */
    @Override
    public ListIterator<E> listIterator(int index) {
        return ImmutableListIterator.create(this.linkedList.listIterator(index));
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#offer(java.lang.Object)
     */
    @Override
    public boolean offer(E e) {
        throw new UnsupportedOperationException("Offer operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#offerFirst(java.lang.Object)
     */
    @Override
    public boolean offerFirst(E e) {
        throw new UnsupportedOperationException("OfferFirst operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#offerLast(java.lang.Object)
     */
    @Override
    public boolean offerLast(E e) {
        throw new UnsupportedOperationException("OfferLast operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#peek()
     */
    @Override
    public E peek() {
        return this.linkedList.peek();
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#peekFirst()
     */
    @Override
    public E peekFirst() {
        return this.linkedList.peekFirst();
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#peekLast()
     */
    @Override
    public E peekLast() {
        return this.linkedList.peekLast();
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#poll()
     */
    @Override
    public E poll() {
        throw new UnsupportedOperationException("Poll operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#pollFirst()
     */
    @Override
    public E pollFirst() {
        throw new UnsupportedOperationException("PollFirst operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#pollLast()
     */
    @Override
    public E pollLast() {
        throw new UnsupportedOperationException("PollLast operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#pop()
     */
    @Override
    public E pop() {
        throw new UnsupportedOperationException("Pop operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#push(java.lang.Object)
     */
    @Override
    public void push(E e) {
        throw new UnsupportedOperationException("Push operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#remove()
     */
    @Override
    public E remove() {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#remove(int)
     */
    @Override
    public E remove(int index) {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> collection) {
        throw new UnsupportedOperationException("RemoveAll operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#removeFirst()
     */
    @Override
    public E removeFirst() {
        throw new UnsupportedOperationException("RemoveFirst operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#removeFirstOccurrence(java.lang.Object)
     */
    @Override
    public boolean removeFirstOccurrence(Object o) {
        throw new UnsupportedOperationException("RemoveFirstOccurrence operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#removeLast()
     */
    @Override
    public E removeLast() {
        throw new UnsupportedOperationException("RemoveLast operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#removeLastOccurrence(java.lang.Object)
     */
    @Override
    public boolean removeLastOccurrence(Object o) {
        throw new UnsupportedOperationException("RemoveLastOccurrence operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> collection) {
        throw new UnsupportedOperationException("RetainAll operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#set(int, java.lang.Object)
     */
    @Override
    public E set(int index, E element) {
        throw new UnsupportedOperationException("Set operation is not allowed in ImmutableLinkedLists.");
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#size()
     */
    @Override
    public int size() {
        return this.linkedList.size();
    }

    /* (non-Javadoc)
     * @see java.util.AbstractList#subList(int, int)
     */
    @Override
    public List<E> subList(int fromIndex, int toIndex) {
        return ImmutableCreator.create(this.linkedList.subList(fromIndex, toIndex));
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#toArray()
     */
    @Override
    public Object[] toArray() {
        return this.linkedList.toArray();
    }

    /* (non-Javadoc)
     * @see java.util.LinkedList#toArray(java.lang.Object[])
     */
    @Override
    public <B> B[] toArray(B[] a) {
        return this.linkedList.toArray(a);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#toString()
     */
    @Override
    public String toString() {
        return this.linkedList.toString();
    }

    /* (non-Javadoc)
     * @see java.util.AbstractList#removeRange(int, int)
     */
    @Override
    protected void removeRange(int fromIndex, int toIndex) {
        throw new UnsupportedOperationException("RemoveRange operation is not allowed in ImmutableLinkedLists.");
    }

    @Override
    public void replaceAll(UnaryOperator<E> operator) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedLists.");
    }

    @Override
    public void sort(Comparator<? super E> c) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedLists.");
    }

    @Override
    public <T> T[] toArray(IntFunction<T[]> generator) {
        return this.linkedList.toArray(generator);
    }

    @Override
    public boolean removeIf(Predicate<? super E> filter) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedLists.");
    }

    @Override
    public void add(int index, E element) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedLists.");
    }

    @Override
    public Spliterator<E> spliterator() {
        return this.linkedList.spliterator();
    }
}
