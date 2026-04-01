package immutables;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.stream.Stream;

/**
 * An immutable set implementation offering random access by an index. The indices of the elements correspond to the 
 * insertion order of the elements.
 * @author cryingshadow
 * @version $Id$
 * @param <E> The type of the elements.
 */
public class ImmutableRandomAccessSet<E> extends AbstractSet<E> implements ImmutableSet<E> {

    /**
     * A list containing the same elements, but allowing random access.
     */
    private final ImmutableList<E> list;

    /**
     * The backing set for this random access set.
     */
    private final ImmutableSet<E> set;

    /**
     * Creates an empty random access set.
     */
    public ImmutableRandomAccessSet() {
        this.set = ImmutableCreator.create(Collections.<E>emptySet());
        this.list = ImmutableCreator.create(Collections.<E>emptyList());
    }

    /**
     * Creates a random access set with the elements in the specified collection. Equivalent to creating an empty 
     * random access set and then adding all elements in the specified collection.
     * @param c Some collection of elements.
     */
    public ImmutableRandomAccessSet(Collection<? extends E> c) {
        this.set = ImmutableCreator.create(new LinkedHashSet<E>(c));
        this.list = ImmutableCreator.create(new ArrayList<E>(this.set));
    }

    @Override
    public void forEach(Consumer<? super E> action)  {
        this.set.forEach(action);
    }

    /**
     * @param index The index of an element.
     * @return The element at the specified index.
     */
    public E get(int index) {
        return this.list.get(index);
    }

    @Override
    public Iterator<E> iterator() {
        final Iterator<E> setIt = this.set.iterator();
        final Iterator<E> listIt = this.list.iterator();
        return
            new Iterator<E>() {

                @Override
                public boolean hasNext() {
                    return listIt.hasNext();
                }

                @Override
                public E next() {
                    setIt.next();
                    return listIt.next();
                }

            };
    }

    @Override
    public int size() {
        return this.set.size();
    }

    @Override
    public Spliterator<E> spliterator() {
        return this.list.spliterator();
    }

    @Override
    public <T> T[] toArray(IntFunction<T[]> generator) {
        return this.list.toArray(generator);
    }

    @Override
    public boolean removeIf(Predicate<? super E> filter) {
        throw new UnsupportedOperationException("Modifications are not allowed in immutable sets.");
    }

    @Override
    public Stream<E> stream() {
        return this.list.stream();
    }

    @Override
    public Stream<E> parallelStream() {
        return this.list.parallelStream();
    }

    @Override
    public boolean equals(Object o) {
        return this.set.equals(o);
    }

    @Override
    public int hashCode() {
        return this.set.hashCode();
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException("Modifications are not allowed in immutable sets.");
    }

    @Override
    public boolean isEmpty() {
        return this.set.isEmpty();
    }

    @Override
    public boolean contains(Object o) {
        return this.set.contains(o);
    }

    @Override
    public Object[] toArray() {
        return this.list.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        return this.list.toArray(a);
    }

    @Override
    public boolean add(E e) {
        throw new UnsupportedOperationException("Modifications are not allowed in immutable sets.");
    }

    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException("Modifications are not allowed in immutable sets.");
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return this.set.containsAll(c);
    }

    @Override
    public boolean addAll(Collection<? extends E> c) {
        throw new UnsupportedOperationException("Modifications are not allowed in immutable sets.");
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException("Modifications are not allowed in immutable sets.");
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException("Modifications are not allowed in immutable sets.");
    }

    @Override
    public String toString() {
        return this.set.toString();
    }
}
