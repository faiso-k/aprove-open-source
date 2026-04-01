package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

/**
 * Concatenates two or more <code>Iterable</code>s.
 *
 * @author noschinski
 * @version $Id$
 * @param <A> Type of the <code>Iterable</code>s
 */
public class IterableConcatenator<A> implements Iterable<A> {
    private final Iterable<? extends Iterable<A>> iterables;

    private IterableConcatenator(Iterable<? extends Iterable<A>> iterables) {
        this.iterables = iterables;
    }

    /**
     * Creates an Iterable which concatenates two Iterables
     */
    public static <A> IterableConcatenator<A>
            create(Iterable<A> i1, Iterable<A> i2) {
        List<Iterable<A>> iterables = new LinkedList<Iterable<A>>();
        iterables.add(i1);
        iterables.add(i2);
        return new IterableConcatenator<A>(iterables);
    }

    /**
     * Creates an Iterable by concatenating all elements of
     * <code>iterables</code>.
     */
    public static <A> IterableConcatenator<A>
            create(Iterable<? extends Iterable<A>> iterables) {
        return new IterableConcatenator<A>(iterables);
    }

    /**
     * Returns the iterator
     */
    @Override
    public Iterator<A> iterator() {
        return new Iterator<A>() {
            private Iterator<? extends Iterable<A>> outer = IterableConcatenator.this.iterables.iterator();
            private Iterator<A> inner = null;

            @Override
            public boolean hasNext() {
                if (this.inner != null && this.inner.hasNext()) {
                    return true;
                }

                while (this.outer.hasNext()) {
                    this.inner = this.outer.next().iterator();
                    if (this.inner.hasNext()) {
                        return true;
                    }
                }
                return false;
            }

            @Override
            public A next() {
                if (this.inner != null && this.inner.hasNext()) {
                    return this.inner.next();
                }
                while (this.outer.hasNext()) {
                    this.inner = this.outer.next().iterator();
                    if (this.inner.hasNext()) {
                        return this.inner.next();
                    }
                }
                throw new NoSuchElementException();
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }

        };
    }
}
