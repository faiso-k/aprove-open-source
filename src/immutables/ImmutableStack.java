package immutables;

import java.util.Collection;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Stack;
import java.util.function.Consumer;
import java.util.stream.*;

/**
 * @author marinag
 *
 */
public class ImmutableStack<E> extends Stack<E> implements ImmutableCollection<E>, Immutable {
    private final Stack<E> stack;
    private int hashValue;
    private boolean hashValid;

    @Override
    public Stream<E> stream() {
        return this.stack.stream();
    }

    @Override
    public Stream<E> parallelStream() {
        return this.stack.parallelStream();
    }

    /**
     * Creates an empty Stack.
     */
    private ImmutableStack(final Stack<E> referenceStack) {
        super();
        this.stack = referenceStack;
        this.hashValid = false;
    }

    static <E> ImmutableStack<E> create(final Stack<E> referenceStack) {
        if (referenceStack instanceof ImmutableStack) {
            return (ImmutableStack<E>) referenceStack;
        }
        return new ImmutableStack<E>(referenceStack);
    }

    //    static <E> ImmutableStack<E> create(final ImmutableStack<E> referenceStack) {
    //        return referenceStack;
    //    }

    @Override
    public E push(final E item) {
        throw new UnsupportedOperationException("Push operation is not allowed in ImmutableStack.");
    }

    @Override
    public synchronized E pop() {
        throw new UnsupportedOperationException("Push operation is not allowed in ImmutableStack.");
    }

    @Override
    public synchronized E peek() {

        return this.stack.peek();
    }

    public ImmutableStack<E> doPop() {

        final Stack<E> copy = (Stack<E>) this.stack.clone();
        copy.pop();
        return create(copy);
    }

    public ImmutableStack<E> doPush(final E item) {

        final Stack<E> copy = (Stack<E>) this.stack.clone(); //new Stack<E>();
        //copy.addAll(this.stack);
        copy.push(item);
        return create(copy);
    }

    @Override
    public boolean empty() {

        return this.isEmpty();
    }

    @Override
    public void forEach(Consumer<? super E> action)  {
        this.stack.forEach(action);
    }

    @Override
    public synchronized int search(final Object o) {

        return this.stack.search(o);
    }

    @Override
    public int hashCode() {
        if (this.hashValid) {
            return this.hashValue;
        } else {
            this.hashValue = this.stack.hashCode();
            this.hashValid = true;
            return this.hashValue;
        }
    }

    @Override
    public boolean equals(final Object o) {
        if (!(o instanceof List)) {
            return false;
        }
        final Stack<?> other = (Stack<?>) o;
        if (other.hashCode() != this.hashCode()) {
            return false;
        }
        return this.stack.equals(other);
    }

    @Override
    public synchronized void copyInto(final Object[] anArray) {
        System.arraycopy(this.elementData, 0, anArray, 0, this.elementCount);
    }

    @Override
    public synchronized void trimToSize() {
        this.stack.trimToSize();
    }

    @Override
    public synchronized void ensureCapacity(final int minCapacity) {
        this.stack.ensureCapacity(minCapacity);
    }

    @Override
    public synchronized void setSize(final int newSize) {
        throw new UnsupportedOperationException("setSize operation is not allowed in ImmutableStack.");
    }

    @Override
    public synchronized int capacity() {
        return this.stack.capacity();
    }

    @Override
    public synchronized int size() {
        return this.stack.size();
    }

    @Override
    public synchronized boolean isEmpty() {
        return this.stack.isEmpty();
    }

    @Override
    public Enumeration<E> elements() {
        return this.stack.elements();
    }

    @Override
    public boolean contains(final Object o) {
        return this.stack.contains(o);
    }

    @Override
    public int indexOf(final Object o) {
        return this.stack.indexOf(o);
    }

    @Override
    public synchronized int indexOf(final Object o, final int index) {
        return this.indexOf(o, index);
    }

    @Override
    public synchronized int lastIndexOf(final Object o) {
        return lastIndexOf(o, this.elementCount - 1);
    }

    @Override
    public synchronized int lastIndexOf(final Object o, final int index) {
        return this.stack.lastIndexOf(o, index);
    }

    @Override
    public synchronized E elementAt(final int index) {
        return this.stack.elementAt(index);
    }

    @Override
    public synchronized E firstElement() {
        return this.stack.firstElement();
    }

    @Override
    public synchronized E lastElement() {
        return this.stack.lastElement();
    }

    @Override
    public synchronized void setElementAt(final E obj, final int index) {
        throw new UnsupportedOperationException("setElement operation is not allowed in ImmutableStack.");
    }

    @Override
    public synchronized void removeElementAt(final int index) {
        throw new UnsupportedOperationException("remobeElement operation is not allowed in ImmutableStack.");
    }

    @Override
    public synchronized void insertElementAt(final E obj, final int index) {
        throw new UnsupportedOperationException("insertElementAt operation is not allowed in ImmutableStack.");
    }

    @Override
    public synchronized void addElement(final E obj) {
        throw new UnsupportedOperationException("addElement operation is not allowed in ImmutableStack.");
    }

    @Override
    public synchronized boolean removeElement(final Object obj) {
        throw new UnsupportedOperationException("removeElement operation is not allowed in ImmutableStack.");
    }

    @Override
    public synchronized void removeAllElements() {

        throw new UnsupportedOperationException("removeAllElements operation is not allowed in ImmutableStack.");
    }

    @Override
    public synchronized Object clone() {
        return this;
    }

    @Override
    public synchronized Object[] toArray() {
        return this.stack.toArray();
    }

    @Override
    public synchronized <T> T[] toArray(final T[] a) {
        return this.stack.toArray(a);
    }

    @Override
    public synchronized E get(final int index) {
        return this.get(index);
    }

    @Override
    public synchronized E set(final int index, final E element) {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public synchronized boolean add(final E e) {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public boolean remove(final Object o) {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public void add(final int index, final E element) {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public synchronized E remove(final int index) {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public void clear() {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public synchronized boolean containsAll(final Collection<?> c) {
        return this.stack.containsAll(c);
    }

    @Override
    public synchronized boolean addAll(final Collection<? extends E> c) {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public synchronized boolean removeAll(final Collection<?> c) {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public synchronized boolean retainAll(final Collection<?> c) {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public synchronized boolean addAll(final int index, final Collection<? extends E> c) {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public synchronized String toString() {
        return this.stack.toString();
    }

    @Override
    public synchronized List<E> subList(final int fromIndex, final int toIndex) {
        return ImmutableCreator.create(this.stack.subList(fromIndex, toIndex));
    }

    @Override
    protected synchronized void removeRange(final int fromIndex, final int toIndex) {
        throw new ImmutableUnsupOpException();
    }

    @Override
    public synchronized ListIterator<E> listIterator(final int index) {
        return ImmutableListIterator.create(this.stack.listIterator(index));
    }

    @Override
    public synchronized ListIterator<E> listIterator() {
        return ImmutableListIterator.create(this.stack.listIterator());
    }

    @Override
    public synchronized Iterator<E> iterator() {
        return ImmutableIterator.create(this.stack.iterator());
    }

}
