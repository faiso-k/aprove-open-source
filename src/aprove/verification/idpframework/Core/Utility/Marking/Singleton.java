package aprove.verification.idpframework.Core.Utility.Marking;

import java.lang.reflect.*;
import java.util.*;

import immutables.*;


/**
 * @author MP
 */
public class Singleton<T> implements MarkContent<Singleton<T>, T>,
        ImmutableCollection<T> {

    private final T content;

    public Singleton(final T content) {
        this.content = content;
    }

    public T getContent() {
        return this.content;
    }

    @Override
    public int size() {
        return 0;
    }

    @Override
    public Iterator<T> iterator() {
        return new Iterator<T>() {

            boolean first = true;

            @Override
            public boolean hasNext() {
                return this.first;
            }

            @Override
            public T next() {
                this.first = false;
                return Singleton.this.content;
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException("immutable");
            }

        };
    }

    @Override
    public ImmutableCollection<T> asCollection() {
        return this;
    }

    @Override
    public boolean add(final T e) {
        throw new UnsupportedOperationException("immutable");
    }

    @Override
    public boolean addAll(final Collection<? extends T> c) {
        throw new UnsupportedOperationException("immutable");
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException("immutable");
    }

    @Override
    public boolean contains(final Object o) {
        return this.content.equals(o);
    }

    @Override
    public boolean containsAll(final Collection<?> c) {
        for (final Object obj : c) {
            if (!obj.equals(this.content)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean isEmpty() {
        return false;
    }

    @Override
    public boolean isSingleton(final T content) {
        return this.content.equals(content);
    }

    @Override
    public boolean remove(final Object o) {
        throw new UnsupportedOperationException("immutable");
    }

    @Override
    public boolean removeAll(final Collection<?> c) {
        throw new UnsupportedOperationException("immutable");
    }

    @Override
    public boolean retainAll(final Collection<?> c) {
        throw new UnsupportedOperationException("immutable");
    }

    @Override
    public Object[] toArray() {
        return new Object[] { this.content };
    }

    @SuppressWarnings("unchecked")
    @Override
    public <U> U[] toArray(U[] contents) {
        if (contents.length < 1) {
            final Class<?> ct = contents.getClass().getComponentType();
            contents = (U[]) Array.newInstance(ct, 1);
        }
        contents[0] = (U) this.content;
        if (contents.length > 1) {
            contents[1] = null;
        }
        return contents;
    }

}
