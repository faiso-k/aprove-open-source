package aprove.verification.idpframework.Core.Utility;

import java.util.*;

import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author MP
 */
public class DoubleKeyCollectionMap<K1, K2, V> extends LinkedHashMap<K1, CollectionMap<K2, V>> {

    /**
     *
     */
    private static final long serialVersionUID = 1L;

    @SuppressWarnings("rawtypes")
    private CollectionCreator<V, ? extends Collection<V>> collectionCreator;

    public DoubleKeyCollectionMap() {
        this(CollectionCreator.linkedHashSet());
    }

    public DoubleKeyCollectionMap(CollectionCreator<V, ? extends Collection<V>> collectionCreator) {
        this.collectionCreator = collectionCreator;
    }

    public boolean add (final K1 k1, final K2 k2, final V value) {
        return this.getCollectionMap(k1, true).add(k2, value);
    }

    public boolean add (final Map<K1, ? extends Map<? extends K2, ? extends Collection<V>>> values) {
        boolean res = false;
        for (final Map.Entry<K1, ? extends Map<? extends K2, ? extends Collection<V>>> vEntry : values.entrySet()) {
            res = this.add(vEntry.getKey(), vEntry.getValue());
        }
        return res;
    }

    public boolean add (final K1 k1, final Map<? extends K2, ? extends Collection<V>> values) {
        boolean res = false;
        for (final Map.Entry<? extends K2, ? extends Collection<V>> vEntry : values.entrySet()) {
            res = this.getCollectionMap(k1, true).add(vEntry.getKey(), vEntry.getValue()) || res;
        }
        return res;
    }

    public boolean containsKey(final K1 k1, final K2 k2) {
        final CollectionMap<K2, V> map = this.getCollectionMap(k1, false);
        if (map != null) {
            return map.containsKey(k2);
        } else {
            return false;
        }
    }

    public boolean contains(final K1 k1, final K2 k2, final V value) {
        final CollectionMap<K2, V> map = this.getCollectionMap(k1, false);
        if (map != null) {
            return map.contains(k2, value);
        } else {
            return false;
        }
    }

    /**
     * Used to port from Java 7 to Java 8.
     * The current method removeFromCollection used to be named remove,
     * clashing with the method Map.remove introduced in Java 8.
     * This method decides in runtime whether to behave like
     * Map.remove or removeFromCollection based on the arguments.
     * Use should be avoided in favour of
     * removeFromCollection or the single-argument variant of Map.remove.
     */
    @Override
    //@Override
    @Deprecated
    public boolean remove(Object k1, Object k2_or_v) {
        final CollectionMap<K2, V> map = this.get(k1);
        if (map == null) {
            return false;
        } else if (map.values().contains(k2_or_v)) {
            return map.remove(k2_or_v) != null;
        } else if (map.equals(k2_or_v)) {
            return this.remove(k2_or_v) != null;
        } else {
            return false;
        }
    }

    public Collection<V> removeFromCollection(final K1 k1, final K2 k2) {
        final CollectionMap<K2, V> map = this.getCollectionMap(k1, false);
        if (map != null) {
            return map.remove(k2);
        } else {
            return null;
        }
    }

    public boolean remove(final K1 k1, final K2 k2, final V value) {
        final CollectionMap<K2, V> map = this.getCollectionMap(k1, false);
        if (map != null) {
            return map.remove(k2, value);
        } else {
            return false;
        }
    }

    private CollectionMap<K2, V> getCollectionMap(final K1 k1, final boolean createNew) {
        CollectionMap<K2, V> res = this.get(k1);
        if (res == null && createNew) {
            res = new CollectionMap<K2, V>(collectionCreator);
            this.put(k1, res);
        }
        return res;
    }

}
