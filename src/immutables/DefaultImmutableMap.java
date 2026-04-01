package immutables;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * Default implementation for ImmutableMap, handy if you want to create
 * immutable map for a map which has no corresponding immutable class of
 * its own. Still, you can only use (non-destructive!) methods already
 * specified by Map.
 *
 * @author Martin Mertens, Carsten Fuhs
 * @version $Id$
 * @param <K> The type of the map's keys.
 * @param <V> The type of the map's values.
 */
class DefaultImmutableMap<K,V> implements ImmutableMap<K,V> {

    /**
     * @param <L> The type of the map's keys.
     * @param <W> The type of the map's values.
     * @param reference The Map to be made immutable.
     * @return An immutable version of the specified Map.
     */
    static <L,W> DefaultImmutableMap<L,W> create(DefaultImmutableMap<L,W> reference) {
        return reference;
    }
    
    /**
     * @param <L> The type of the map's keys.
     * @param <W> The type of the map's values.
     * @param reference The Map to be made immutable.
     * @return An immutable version of the specified Map.
     */
    static <L,W> DefaultImmutableMap<L,W> create(Map<L,W> reference) {
        return new DefaultImmutableMap<L,W>(reference);
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
     * @param reference The Map to be made immutable.
     */
    private DefaultImmutableMap(Map<K,V> reference) {
        this.map = reference;
        this.hashValid = false;
    }

    /* (non-Javadoc)
     * @see java.util.Map#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException("Clear operation is not allowed in ImmutableMaps.");
    }

    /* (non-Javadoc)
     * @see java.lang.Object#clone()
     */
    @Override
    public Object clone() {
        return this;
    }

    /* (non-Javadoc)
     * @see java.util.Map#containsKey(java.lang.Object)
     */
    @Override
    public boolean containsKey(Object key) {
        return this.map.containsKey(key);
    }

    /* (non-Javadoc)
     * @see java.util.Map#containsValue(java.lang.Object)
     */
    @Override
    public boolean containsValue(Object value) {
        return this.map.containsValue(value);
    }

    /* (non-Javadoc)
     * @see java.util.Map#entrySet()
     */
    @Override
    public Set<Entry<K, V>> entrySet() {
        return ImmutableCreator.create(this.map.entrySet());
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
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
     * @see java.util.Map#get(java.lang.Object)
     */
    @Override
    public V get(Object object) {
        return this.map.get(object);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
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
     * @see java.util.Map#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return this.map.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.util.Map#keySet()
     */
    @Override
    public Set<K> keySet() {
        return ImmutableCreator.create(this.map.keySet());
    }

    /* (non-Javadoc)
     * @see java.util.Map#put(java.lang.Object, java.lang.Object)
     */
    @Override
    public V put(K arg0, V arg1) {
        throw new UnsupportedOperationException("Put operation is not allowed in ImmutableMaps.");
    }

    /* (non-Javadoc)
     * @see java.util.Map#putAll(java.util.Map)
     */
    @Override
    public void putAll(Map<? extends K, ? extends V> arg0) {
        throw new UnsupportedOperationException("PutAll operation is not allowed in ImmutableMaps.");        
    }

    /* (non-Javadoc)
     * @see java.util.Map#remove(java.lang.Object)
     */
    @Override
    public V remove(Object arg0) {
        throw new UnsupportedOperationException("Remove operation is not allowed in ImmutableMaps.");
    }

    /* (non-Javadoc)
     * @see java.util.Map#size()
     */
    @Override
    public int size() {
        return this.map.size();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.map.toString();
    }

    /* (non-Javadoc)
     * @see java.util.Map#values()
     */
    @Override
    public Collection<V> values() {
        return ImmutableCreator.create(this.map.values());
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
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableMaps.");
    }

    @Override
    public V putIfAbsent(K key, V value) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableMaps.");
    }

    @Override
    public boolean remove(Object key, Object value) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableMaps.");
    }

    @Override
    public boolean replace(K key, V oldValue, V newValue) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableMaps.");
    }

    @Override
    public V replace(K key, V value) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableMaps.");
    }

    @Override
    public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableMaps.");
    }

    @Override
    public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableMaps.");
    }

    @Override
    public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableMaps.");
    }

    @Override
    public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        throw new UnsupportedOperationException("Modifications are not allowed in ImmutableMaps.");
    }
}
