package aprove.verification.idpframework.Core.Utility;

import java.util.*;

import immutables.*;

/**
 *
 * @author MP
 */
public class ImmutablePairComparator<K extends Comparable<K>, V extends Comparable<V>> implements Comparator<ImmutablePair<K, V>>{

    @Override
    public int compare(final ImmutablePair<K, V> o1, final ImmutablePair<K, V> o2) {
        final int xCompare = o1.x.compareTo(o2.x);
        if (xCompare != 0) {
            return xCompare;
        }

        return o1.y.compareTo(o2.y);
    }

}
