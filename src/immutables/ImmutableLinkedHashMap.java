package immutables;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.*;

/**
 * Class representing a LinkedHashMap which, once instantiated with a reference
 * LinkedHashMap, does not support any put, putAll, remove or clear operation.
 * It wraps a mutable LinkedHashMap and relegates to this map's
 * operations if they do not change any contents of the entry set. Otherwise,
 * an UnsupportedOperationException is thrown, indicating that this operation
 * should not be used by the programmer. <p>
 *
 * @author Martin Mertens, Carsten Fuhs
 * @version $Id$
 * @param <K> The type of the map's keys.
 * @param <V> The type of the map's values.
 */
public class ImmutableLinkedHashMap<K,V> extends LinkedHashMap<K,V> implements ImmutableMap<K,V> {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 2888495830665768050L;

    /**
     * @param <L> The type of the map's keys.
     * @param <W> The type of the map's values.
     * @param reference The LinkedHashMap to be made immutable.
     * @return An immutable version of the specified LinkedHashMap.
     */
    static <L,W> ImmutableLinkedHashMap<L,W> create(ImmutableLinkedHashMap<L,W> reference) {
        return reference;
    }

    /**
     * @param <L> The type of the map's keys.
     * @param <W> The type of the map's values.
     * @param reference The LinkedHashMap to be made immutable.
     * @return An immutable version of the specified LinkedHashMap.
     */
    static <L,W> ImmutableLinkedHashMap<L,W> create(LinkedHashMap<L,W> reference) {
        return new ImmutableLinkedHashMap<L,W>(reference);
    }

    /**
     * Has the hash value already been computed?
     */
    private boolean hashValid;

    /**
     * Cache for the hash value.
     */
    private int hashValue;

    /**
     * Reference is stored and may not be modified by this class.
     */
    private final Map<K,V> map;

    /**
     * @param reference The LinkedHashMap to be made immutable.
     */
    private ImmutableLinkedHashMap(LinkedHashMap<K,V> reference) {
        super(0);
        this.map = reference;
        this.hashValid = false;
    }

    /* (non-Javadoc)
     * @see java.util.LinkedHashMap#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException("Clear operation is not allowed in ImmutableLinkedHashMaps.");
    }

    /* (non-Javadoc)
     * @see java.util.HashMap#clone()
     */
    @Override
    public Object clone() {
        return this;
    }

    /* (non-Javadoc)
     * @see java.util.HashMap#containsKey(java.lang.Object)
     */
    @Override
    public boolean containsKey(Object key) {
        return this.map.containsKey(key);
    }

    /* (non-Javadoc)
     * @see java.util.LinkedHashMap#containsValue(java.lang.Object)
     */
    @Override
    public boolean containsValue(Object value) {
        return this.map.containsValue(value);
    }

    /* (non-Javadoc)
     * @see java.util.HashMap#entrySet()
     */
    @Override
    public Set<Entry<K, V>> entrySet() {
        return ImmutableCreator.create(this.map.entrySet());
    }

    /* (non-Javadoc)
     * @see java.util.AbstractMap#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (! (o instanceof Map)) {
            return false;
        }
        Map<?,?> other = (Map<?,?>) o;
        if (other.hashCode() != this.hashCode()) {
            return false;
        }
        return this.map.equals(other);
    }

    /* (non-Javadoc)
     * @see java.util.LinkedHashMap#get(java.lang.Object)
     */
    @Override
    public V get(Object object) {
        return this.map.get(object);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractMap#hashCode()
     */
    @Override
    public int hashCode() {
        if (this.hashValid) {
            return this.hashValue;
        }
        else {
            this.hashValue = this.map.hashCode();
            this.hashValid = true;
            return this.hashValue;
        }
    }

    /* (non-Javadoc)
     * @see java.util.HashMap#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.map.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.HashMap#keySet()
     */
    @Override
    public Set<K> keySet() {
        return ImmutableCreator.create(this.map.keySet());
    }

    /* (non-Javadoc)
     * @see java.util.HashMap#put(java.lang.Object, java.lang.Object)
     */
    @Override
    public V put(K arg0, V arg1) {
        throw new UnsupportedOperationException("Put operation is not allowed in ImmutableLinkedHashMaps.");
    }

    /* (non-Javadoc)
     * @see java.util.HashMap#putAll(java.util.Map)
     */
    @Override
    public void putAll(Map<? extends K, ? extends V> arg0) {
        throw new UnsupportedOperationException("PutAll operation is not allowed in ImmutableLinkedHashMaps.");
    }

    /* (non-Javadoc)
     * @see java.util.HashMap#remove(java.lang.Object)
     */
    @Override
    public V remove(Object arg0) {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableLinkedHashMaps.");
    }

    /* (non-Javadoc)
     * @see java.util.HashMap#size()
     */
    @Override
    public int size() {
        return this.map.size();
    }

    /* (non-Javadoc)
     * @see java.util.AbstractMap#toString()
     */
    @Override
    public String toString() {
        return this.map.toString();
    }

    /* (non-Javadoc)
     * @see java.util.HashMap#values()
     */
    @Override
    public Collection<V> values() {
        return ImmutableCreator.create(this.map.values());
    }

    /* (non-Javadoc)
     * @see java.util.LinkedHashMap#removeEldestEntry(java.util.Map.Entry)
     */
    @Override
    protected boolean removeEldestEntry(Map.Entry<K,V> eldest) {
        return false;
    }

    @Override
    public V getOrDefault(Object key, V defaultValue) {
        return this.map.getOrDefault(key, defaultValue);
    }

    @Override
    public void forEach(BiConsumer<? super K, ? super V> action) {
        this.map.forEach(action);
    }

    @Override
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedHashMaps.");
    }

    @Override
    public V putIfAbsent(K key, V value) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedHashMaps.");
    }

    @Override
    public boolean remove(Object key, Object value) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedHashMaps.");
    }

    @Override
    public boolean replace(K key, V oldValue, V newValue) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedHashMaps.");
    }

    @Override
    public V replace(K key, V value) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedHashMaps.");
    }

    @Override
    public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedHashMaps.");
    }

    @Override
    public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedHashMaps.");
    }

    @Override
    public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedHashMaps.");
    }

    @Override
    public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableLinkedHashMaps.");
    }
}
