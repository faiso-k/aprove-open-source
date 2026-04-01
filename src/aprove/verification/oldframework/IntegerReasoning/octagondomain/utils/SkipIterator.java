package aprove.verification.oldframework.IntegerReasoning.octagondomain.utils;

import java.util.*;

public class SkipIterator<T> implements Iterator<T> {

    private final Iterator<T> backingIterator;

    public SkipIterator(final Iterator<T> backingIterator) {
        this.backingIterator = backingIterator;
    }

    @Override
    public boolean hasNext() {
        return this.backingIterator.hasNext();
    }

    @Override
    public T next() {
        if (this.backingIterator.hasNext()) {
            final T returnValue = this.backingIterator.next();
            if (this.backingIterator.hasNext()) {
                this.backingIterator.next();
            }
            return returnValue;
        }
        throw new NoSuchElementException();
    }

    @Override
    public void remove() {
        assert false : "Operation not supported";
    }

}
