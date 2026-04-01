package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This map (let's call it aMap) should be used when you need a normal map
 * (let's call it bMap) which value would be a collection. The only difference
 * to a bMap which would look like LinkedHashMap&lt;K,Collection&lt;V&gt;&gt; is the
 * modified put-operation which puts an item of type K into the collection which
 * one would retreive by bMap.get(value) or into a new empty collection if
 * bMap.get(value) returns null which is then put into the map. K: key V:
 * collection item
 * @param <K> type of the keys
 * @param <V> type of the values inside the collection
 * @author Matthias Sondermann
 * @version $Id$
 */
public final class CollectionMap<K, V> extends LinkedHashMap<K, Collection<V>> {

    /**
     * Some unique ID.
     */
    private static final long serialVersionUID = 2070549326475892283L;

    /**
     * The creator used to construct the inner collection.
     */
    private final CollectionCreator<V, ? extends Collection<V>> collectionCreator;

    /**
     * Create a collection map using a LinkedHashSet.
     */
    public CollectionMap() {
        this(CollectionCreator.linkedHashSet());
    }

    /**
     * Creates a collection map using the specified creator
     * @param collectionCreator
     */
    public CollectionMap(CollectionCreator<V, ? extends Collection<V>> collectionCreator) {
        this.collectionCreator = collectionCreator;
    }

    /**
     * Create a new map with data copied from the original map
     * @param original some collection map
     */
    public CollectionMap(final CollectionMap<K, V> original) {
        this(original.collectionCreator);
        this.putAll(original);
    }

    /**
     * Add all items of vv into the collection which is the value of k. If there
     * is no entry for k, a new collection is created and put into the map.
     * @param k Key
     * @param vs Collection items
     * @return true iff this collection changed as a result of the call
     */
    public boolean add(final K k, final Collection<V> vs) {
        Collection<V> vv = this.get(k);
        if (vv == null) {
            vv = this.collectionCreator.create(vs);
            this.put(k, vv);
            return true;
        } else {
            return vv.addAll(vs);
        }
    }

    /**
     * Puts v either into the collection which is returned by this.get(k) or
     * into a new collection which then is put into the map.
     * @param k Key
     * @param v Collection item
     * @return Returns true if the collection changed as a result of the call.
     * Returns false if the collection does not permit duplicates and already
     * contains the specified element.
     */
    public boolean add(final K k, final V v) {
        Collection<V> vv = this.get(k);
        if (vv == null) {
            vv = this.collectionCreator.create();
            this.put(k, vv);
        }
        return vv.add(v);
    }

    /**
     * @return the union of all collections
     */
    public Collection<V> allValues() {
        return allValues(this.collectionCreator);
    }

    /**
     * @return the union of all collections
     */
    public <C extends Collection<V>> C allValues(CollectionCreator<V, C> collectionCreator) {
        final C result = collectionCreator.create();
        for (final Collection<V> vals : this.values()) {
            result.addAll(vals);
        }
        return result;
    }

    /**
     * Check if a value is in the collection specified by the key.
     * @param key the key
     * @param value the value to check for
     * @return true iff the map contains a collection for <code>key</code> and
     *  this collection contains the value <code>value</code>
     */
    public boolean contains(final K key, final V value) {
        final Collection<V> col = this.get(key);
        if (col != null) {
            final boolean result = col.contains(value);
            if (Globals.useAssertions) {
                // Sanity check
                boolean found = false;
                for (final V v : col) {
                    if (v == null) {
                        if (value == null) {
                            found = true;
                            break;
                        }
                    } else if (v.equals(value)) {
                        found = true;
                        break;
                    }
                }
                assert result == found : "inconsistent contains.... did some hashCode change?";
            }
            return result;
        }
        return false;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final CollectionMap<?, ?> other = (CollectionMap<?, ?>) obj;

        if (this.collectionCreator == null) {
            if (other.collectionCreator != null) {
                return false;
            }
        } else if (!this.collectionCreator.equals(other.collectionCreator)) {
            return false;
        }
        return true;
    }

    /**
     * If the collection does not exist, a new empty collection is returned but
     * not (!) stored in the mapping.
     * @param k Key
     * @return The value of k if it exists, a new empty collection otherwise.
     */
    public Collection<V> getNotNull(final K k) {
        Collection<V> vv = this.get(k);
        if (vv == null) {
            vv = this.collectionCreator.create();
        }
        return vv;
    }

    /**
     * If the collection does not exist, a new empty collection is returned and
     * stored in the mapping.
     * @param k Key
     * @return The value of k if it exists, a new empty collection otherwise.
     */
    public Collection<V> getNotNullAndAdd(final K k) {
        final Collection<V> vv = this.getNotNull(k);
        if (vv.isEmpty()) {
            this.put(k, vv);
        }
        return vv;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result =
            prime
                * result
                + ((this.collectionCreator == null) ? 0
                    : this.collectionCreator.hashCode());
        return result;
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
    public boolean remove(final Object key, final Object value) {
        final Collection<V> col = this.get(key);
        if (col == null) {
            return false;
        } else if (col.equals(value)) {
            return this.remove(key) != null;
        } else if (col.contains(value)) {
            return col.remove(value);
        } else {
            return false;
        }
    }

    /**
     * Remove a single value out of the collection specified by the key.
     * @param key the key
     * @param value the value to remove
     * @return true if the value could be removed.
     */
    public boolean removeFromCollection(final K key, final V value) {
        final Collection<V> col = this.get(key);
        if (col != null) {
            return col.remove(value);
        }
        return false;
    }


    /**
     * @return a copy of the collection map (the value collections are cloned, too)
     */
    @Override
    public CollectionMap<K, V> clone() {
        final CollectionMap<K, V> res =
            new CollectionMap<K, V>(this.collectionCreator);
        for (final Map.Entry<K, Collection<V>> entry : this.entrySet()) {
            res.add(entry.getKey(), entry.getValue());
        }

        return res;
    }


    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        final Set<Map.Entry<K, Collection<V>>> entries = this.entrySet();
        if (entries.isEmpty()) {
            return "[empty]";
        }
        final String lineSep = System.getProperty("line.separator");
        for (final Map.Entry<K, Collection<V>> entry : this.entrySet()) {
            sb.append(entry.getKey());
            sb.append(" = ");
            final Iterator<V> it = entry.getValue().iterator();
            if (it.hasNext()) {
                sb.append(it.next());
            }
            while (it.hasNext()) {
                sb.append(", ");
                sb.append(it.next());
            }
            sb.append(lineSep);
        }
        return sb.toString();
    }
}
