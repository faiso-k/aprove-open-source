package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.stream.*;

/**
 * Class representing a LinkedHashSet which, once instantiated with a reference
 * LinkedHashSet, does not support any add, remove, clear or retain operation.
 * It wraps a mutable LinkedHashSet and relegates to this set's operations if
 * they do not change any contents of this set. Otherwise, an
 * UnsupportedOperationException is thrown, indicating that this operation
 * should not be used by the programmer.
 *
 * @author Peter Schneider-Kamp
 * @version $Id$
 * @param <E> The type of the set's elements.
 */
public class ImmutableLinkedHashSet<E> extends LinkedHashSet<E> implements ImmutableSet<E> {

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
    private static final long serialVersionUID = -5272396362466862819L;

    /**
     * @param <U> The type of the elements in the created set.
     * @param referenceSet The LinkedHashSet to be made immutable.
     * @return An immutable version of the specified LinkedHashSet.
     */
    static <U> ImmutableLinkedHashSet<U> create(ImmutableLinkedHashSet<U> referenceSet) {
        return referenceSet;
    }

    /**
     * @param <U> The type of the elements in the created set.
     * @param referenceSet The LinkedHashSet to be made immutable.
     * @return An immutable version of the specified LinkedHashSet.
     */
    static <U> ImmutableLinkedHashSet<U> create(LinkedHashSet<U> referenceSet) {
        return new ImmutableLinkedHashSet<U>(referenceSet);
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
    private final LinkedHashSet<E> set;

    /**
     * @param reference The LinkedHashSet to be made immutable.
     */
    private ImmutableLinkedHashSet(LinkedHashSet<E> reference) {
        super(0);
        this.set = reference;
        this.hashValid = false;
    }

    @Override
    public boolean add(E o) {
        throw new UnsupportedOperationException("Add operation is not allowed in ImmutableLinkedHashSets.");
    }

    @Override
    public boolean addAll(Collection<? extends E> c) {
        throw new UnsupportedOperationException("AddAll operation is not allowed in ImmutableLinkedHashSets.");
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException("Clear operation is not allowed in ImmutableLinkedHashSets.");
    }

    @Override
    public Object clone() {
        return this;
    }

    @Override
    public boolean contains(Object o) {
        return this.set.contains(o);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return this.set.containsAll(c);
    }

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

    @Override
    public boolean isEmpty() {
        return this.set.isEmpty();
    }

    @Override
    public Iterator<E> iterator() {
        return ImmutableIterator.create(this.set.iterator());
    }

    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableLinkedHashSets.");
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException("RemoveAll operation is not allowed in ImmutableLinkedHashSets.");
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException("RetainAll operation is not allowed in ImmutableLinkedHashSets.");
    }
    @Override
    public int size() {
        return this.set.size();
    }

    @Override
    public Object[] toArray() {
        return this.set.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        return this.set.toArray(a);
    }

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
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedHashSets.");
    }

    @Override
    public Spliterator<E> spliterator() {
        return this.set.spliterator();
    }
}
