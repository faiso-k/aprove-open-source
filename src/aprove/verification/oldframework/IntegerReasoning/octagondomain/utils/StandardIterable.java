package aprove.verification.oldframework.IntegerReasoning.octagondomain.utils;

import java.util.*;

/**
 * Useful in cases where we only have an iterator, but want to use that with
 * the standard for(T t : ts) syntax, instead of the more verbose while(it.hasNext())
 * form.
 * @author Alexander Weinert
 */
public class StandardIterable<T> implements Iterable<T> {
    private final Iterator<T> backingIterator;

    public StandardIterable(final Iterator<T> backingIterator) {
        this.backingIterator = backingIterator;
    }

    @Override
    public Iterator<T> iterator() {
        return this.backingIterator;
    }

}
