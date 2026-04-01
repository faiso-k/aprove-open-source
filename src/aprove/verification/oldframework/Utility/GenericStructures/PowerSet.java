package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

import immutables.*;

/**
 * creates an iterator that lazily iterates all subsets
 * of a given set up to a given size. The subsets are
 * ordererd by their size. One can start with small or
 * with large subsets. Based on BasicPowerSet.
 * @author thiemann
 *
 * @param <T>
 */
public class PowerSet<T> implements Iterable<Set<T>> {

    private final ImmutableSet<T> baseSet;
    private final BasicPowerSet   basicPowerSet;

    /**
     * creates a copy if not immutable
     * @param baseSet
     */
    public PowerSet(Set<T> baseSet) {
        this(ImmutableCreator.create(new LinkedHashSet<T>(baseSet)));
    }


    public PowerSet(ImmutableSet<T> baseSet) {
        this.baseSet = baseSet;
        this.basicPowerSet = new BasicPowerSet(this.baseSet.size());
    }

    /**
     * restricts the sizes of the subsets to maxSize,
     * if reverse is true, then large subsets are produced first
     * @param baseSet
     * @param maxSize
     * @param reverse
     */
    public PowerSet(ImmutableSet<T> baseSet, int maxSize, boolean reverse) {
        this.baseSet = baseSet;
        this.basicPowerSet = new BasicPowerSet(this.baseSet.size(), maxSize, reverse);
    }

    @Override
    public Iterator<Set<T>> iterator() {
        final Iterator<boolean[]> basicPowerSetIterator = this.basicPowerSet.iterator();
        return new Iterator<Set<T>>() {

            @Override
            public boolean hasNext() {
                return basicPowerSetIterator.hasNext();
            }

            @Override
            public Set<T> next() {
                boolean[] elementVector = basicPowerSetIterator.next();
                Set<T> result = new LinkedHashSet<T>();
                int i = 0;
                for (T elem : PowerSet.this.baseSet) {
                    if (elementVector[i]) {
                        result.add(elem);
                    }
                    i++;
                }
                return result;
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }

        };
    }


}
