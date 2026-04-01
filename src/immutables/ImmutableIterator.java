package immutables;

import java.util.*;
import java.util.function.Consumer;

/**
 * Created on 09.04.2005 by marmer
 * 
 * Class representing an iterator which does not support a remove operation.
 * It is used as a wrapper around a mutable iterator, but overriding its remove
 * operation to throw an exception.
 * 
 * @author Martin Mertens, cryingshadow
 * @version $Id$
 * @param <T> The type of the elements to be iterated over.
 */
class ImmutableIterator<T> implements Iterator<T> {
    
    /**
     * @param <U> The type of the elements to be iterated over.
     * @param reference The Iterator to be made immutable.
     * @return An immutable version of the specified Iterator.
     */
    static <U> ImmutableIterator<U> create(ImmutableIterator<U> reference) {
        return reference;
    }

    /**
     * @param <U> The type of the elements to be iterated over.
     * @param reference The Iterator to be made immutable.
     * @return An immutable version of the specified Iterator.
     */
    static <U> ImmutableIterator<U> create(Iterator<U> reference) {
        return new ImmutableIterator<U>(reference);
    }
    
    /**
     * Iterator reference.
     */
    final Iterator<T> iterator;
    
    /**
     * @param reference Reference iterator.
     */
    ImmutableIterator (Iterator<T> reference) {
        this.iterator = reference;
    }
        
    /* (non-Javadoc)
     * @see java.util.Iterator#hasNext()
     */
    @Override
    public boolean hasNext() {
        return this.iterator.hasNext();
    }

    /* (non-Javadoc)
     * @see java.util.Iterator#next()
     */
    @Override
    public T next() {
        return this.iterator.next();
    }

    /* (non-Javadoc)
     * @see java.util.Iterator#remove()
     */
    @Override
    public void remove() {
        throw new UnsupportedOperationException("Remove operation is not allowed in immutable iterators.");
    }

    @Override
    public void forEachRemaining(Consumer<? super T> action) {
        this.iterator.forEachRemaining(action);
    }
}
