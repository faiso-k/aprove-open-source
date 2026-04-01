package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

public class UnmodifiableIterator<E> implements Iterator<E> {

    private final Iterator<E> backingIterator;

    public UnmodifiableIterator(Iterator <E> backingIterator) {
        this.backingIterator = backingIterator;
    }

    @Override
    public boolean hasNext() {
        return this.backingIterator.hasNext();
    }

    @Override
    public E next() {
        return this.backingIterator.next();
    }

    @Override
    public void remove() {
        throw new UnsupportedOperationException();
   }

}
