package aprove.verification.complexity.CpxIntTrsProblem.Algorithms;

import java.util.*;

import immutables.*;

/**
 * Enumerates all "sublists" of an list (i.e., all lists that are embedded in
 * the list).
 * <p>
 * Requires the list to have (strictly) less than 64 Elements. Although even 63
 * is to large to enumerate, but we could handle it in theory.
 * </p>
 * <p>
 * The returned lists are free to be modified and not shared in any way.
 * </p>
 * @param <T> The type of elements contained.
 */
public class SublistEnumerator<T> implements Iterable<ArrayList<T>> {
    private final ImmutableList<T> elements;

    public SublistEnumerator(ImmutableList<T> elements) {
        this.elements = elements;
        if (elements.size() >= 64) {
            throw new IllegalArgumentException("To many elements to enumerate Sublists.");
        }
    }

    private final class SublistEnumeratorIterator implements Iterator<ArrayList<T>> {

        private final int size;
        private long index;

        private SublistEnumeratorIterator() {
            this.size = SublistEnumerator.this.elements.size();
            this.index = 0;
        }

        @Override
        public boolean hasNext() {
            return this.index < (1 << this.size);
        }

        @Override
        public ArrayList<T> next() {
            if (!this.hasNext()) {
                throw new NoSuchElementException();
            }
            ArrayList<T> sublist = new ArrayList<>();
            for (int i = 0; i < this.size; ++i) {
                if ((((long) 1 << i) & this.index) != 0) {
                    sublist.add(SublistEnumerator.this.elements.get(i));
                }
            }
            ++this.index;
            return sublist;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

    @Override
    public Iterator<ArrayList<T>> iterator() {
        return new SublistEnumeratorIterator();
    }
}
