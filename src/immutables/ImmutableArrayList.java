package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.*;

/**
 * Class representing a ArrayList which, once instantiated with a reference
 * ArrayList, does not support any operations which would change the state
 * of this arrayList.<p>
 * It wraps a mutable ArrayList and relegates to this arrayList's operations if
 * they do not change any contents of this arrayList. Otherwise, an
 * UnsupportedOperationException is thrown, indicating that this operation
 * should not be used by the programmer.
 * @author unknown, cryingshadow
 * @version $Id$
 * @param <A> The type of the list's elements.
 */
public class ImmutableArrayList<A> extends ArrayList<A> implements ImmutableList<A> {

    @Override
    public Stream<A> stream() {
        return this.arrayList.stream();
    }

    @Override
    public Stream<A> parallelStream() {
        return this.arrayList.parallelStream();
    }

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 7550586853469885090L;

    /**
     * @param <U> The type of the elements in the created list.
     * @param referenceArrayList The ArrayList to be made immutable.
     * @return An immutable version of the specified ArrayList.
     */
    static <U> ImmutableArrayList<U> create(ArrayList<U> referenceArrayList) {
        return new ImmutableArrayList<U>(referenceArrayList);
    }

    /**
     * @param <U> The type of the elements in the created list.
     * @param referenceArrayList The ArrayList to be made immutable.
     * @return An immutable version of the specified ArrayList.
     */
    static <U> ImmutableArrayList<U> create(ImmutableArrayList<U> referenceArrayList) {
        return referenceArrayList;
    }

    /**
     * Reference from the constructor, will not be modified by this class.
     */
    private final ArrayList<A> arrayList;

    /**
     * Has hashValue already been computed?
     */
    private boolean hashValid;

    /**
     * Cache for the hash value of this.
     */
    private int hashValue;

    /**
     * @param reference The ArrayList to be made immutable.
     */
    private ImmutableArrayList(ArrayList<A> reference) {
        super(0);
        this.arrayList = reference;
        this.hashValid = false;
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#add(java.lang.Object)
     */
    @Override
    public boolean add(A o) {
        throw new UnsupportedOperationException("Add operation is not allowed in ImmutableArrayLists.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#add(int, java.lang.Object)
     */
    @Override
    public void add(int index, A element) {
        throw new UnsupportedOperationException("Add operation is not allowed in ImmutableArrayLists.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends A> collection) {
        throw new UnsupportedOperationException("AddAll operation is not allowed in ImmutableArrayLists.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#addAll(int, java.util.Collection)
     */
    @Override
    public boolean addAll(int index, Collection<? extends A> c) {
        throw new UnsupportedOperationException("AddAll operation is not allowed in ImmutableArrayLists.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException("Clear operation is not allowed in ImmutableArrayLists.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#clone()
     */
    @Override
    public Object clone() {
        return this;
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#contains(java.lang.Object)
     */
    @Override
    public boolean contains(Object object) {
        return this.arrayList.contains(object);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return this.arrayList.containsAll(c);
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#ensureCapacity(int)
     */
    @Override
    public void ensureCapacity(int minCapacity) {
    }

    /* (non-Javadoc)
     * @see java.util.AbstractList#equals(java.lang.Object)
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
        return this.arrayList.equals(other);
    }

    @Override
    public void forEach(Consumer<? super A> action)  {
        this.arrayList.forEach(action);
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#get(int)
     */
    @Override
    public A get(int index) {
        return this.arrayList.get(index);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractList#hashCode()
     */
    @Override
    public int hashCode() {
        if (this.hashValid) {
            return this.hashValue;
        }
        else {
            this.hashValue = this.arrayList.hashCode();
            this.hashValid = true;
            return this.hashValue;
        }
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#indexOf(java.lang.Object)
     */
    @Override
    public int indexOf(Object elem) {
        return this.arrayList.indexOf(elem);
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.arrayList.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#iterator()
     */
    @Override
    public Iterator<A> iterator() {
        return ImmutableIterator.create(this.arrayList.iterator());
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#lastIndexOf(java.lang.Object)
     */
    @Override
    public int lastIndexOf(Object elem) {
        return this.arrayList.lastIndexOf(elem);
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#listIterator()
     */
    @Override
    public ListIterator<A> listIterator() {
        return ImmutableListIterator.create(this.arrayList.listIterator());
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#listIterator(int)
     */
    @Override
    public ListIterator<A> listIterator(int index) {
        return ImmutableListIterator.create(this.arrayList.listIterator(index));
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#remove(int)
     */
    @Override
    public A remove(int index) {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableArrayLists.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableArrayLists.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> collection) {
        throw new UnsupportedOperationException("RemoveAll operation is not allowed in ImmutableArrayLists.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> collection) {
        throw new UnsupportedOperationException("RetainAll operation is not allowed in ImmutableArrayLists.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#set(int, java.lang.Object)
     */
    @Override
    public A set(int index, A element) {
        throw new UnsupportedOperationException("Set operation is not allowed in ImmutableArrayLists.");
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#size()
     */
    @Override
    public int size() {
        return this.arrayList.size();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#subList(int, int)
     */
    @Override
    public List<A> subList(int fromIndex, int toIndex) {
        return ImmutableCreator.create(this.arrayList.subList(fromIndex, toIndex));
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#toArray()
     */
    @Override
    public Object[] toArray() {
        return this.arrayList.toArray();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#toArray(java.lang.Object[])
     */
    @Override
    public <B> B[] toArray(B[] a) {
        return this.arrayList.toArray(a);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#toString()
     */
    @Override
    public String toString() {
        return this.arrayList.toString();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#trimToSize()
     */
    @Override
    public void trimToSize() {
        this.arrayList.trimToSize();
    }

    /* (non-Javadoc)
     * @see java.util.ArrayList#removeRange(int, int)
     */
    @Override
    protected void removeRange(int fromIndex, int toIndex) {
        throw new UnsupportedOperationException("RemoveRange operation is not allowed in ImmutableArrayLists.");
    }

    @Override
    public <T> T[] toArray(IntFunction<T[]> generator) {
        return this.arrayList.toArray(generator);
    }

    @Override
    public Spliterator<A> spliterator() {
        return this.arrayList.spliterator();
    }

    @Override
    public boolean removeIf(Predicate<? super A> filter) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableArrayLists.");
    }

    @Override
    public void replaceAll(UnaryOperator<A> operator) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableArrayLists.");
    }

    @Override
    public void sort(Comparator<? super A> c) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableArrayLists.");
    }
}
