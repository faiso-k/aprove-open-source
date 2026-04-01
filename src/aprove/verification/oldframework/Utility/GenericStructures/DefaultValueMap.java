package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

/**
 * This map will return a default value whenever a get would otherwise return
 * null. Note that one cannot explicitly assign a null element in such a map;
 * this is intended, as explicitlly assigning null is explicitly assigning the
 * default value.
 * @author Patrick Kabasci
 * @version $Id$
 * @param <V> the type of the values
 * @param <K> the type of the keys
 */
public class DefaultValueMap<K, V> extends LinkedHashMap<K, V> implements
        Map<K, V> {

    /**
     * Some unique ID for serialization.
     */
    private static final long serialVersionUID = 2678043369342084036L;

    /**
     * The default value.
     */
    private V defaultValue;

    /**
     * Create a new map with the given default value.
     * @param newDefaultValue some value used as the default.
     */
    public DefaultValueMap(final V newDefaultValue) {
        this.defaultValue = newDefaultValue;
    }

    /**
     * @param key some key
     * @return the value stored for the key, but return null instead of the
     * return value if it does not exist.
     */
    public V getNoDefault(final Object key) {
        return super.get(key);
    }

    /**
     * @return the value stored for the given key. If that value does not exist,
     * the default value is returned.
     * @param key some key
     */
    @Override
    public V get(final Object key) {
        V res = super.get(key);
        if (res == null) {
            res = this.defaultValue;
        }
        return res;

    }

    /**
     * @return Returns the defaultValue.
     */
    public V getDefaultValue() {
        return this.defaultValue;
    }

    /**
     * @param newDefaultValue The default value to set.
     */
    public void setDefaultValue(final V newDefaultValue) {
        this.defaultValue = newDefaultValue;
    }

    /**
     * @return the string representation of the underlying map and the default
     * value
     */
    @Override
    public String toString() {
        return super.toString() + ", default = " + this.defaultValue;
    }
}

