package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

/** LinkedHashMap that hashes over a pair of objects.
 *
 *  @author  nowonder
 *  @version $Id$
 */
public class DoubleMap<T,U,V> {

    private LinkedHashMap<T,LinkedHashMap<U,V>> map;

    public DoubleMap() {
        this.map = new LinkedHashMap<T,LinkedHashMap<U,V>>();
    }

    /** Maps the pair (s,t) to value */
    public void put(T s, U t, V value) {
        LinkedHashMap<U,V> sMap;
        sMap = this.map.get(s);
        if (sMap == null) {
            sMap = new LinkedHashMap<U,V>();
            this.map.put(s, sMap);
        }
        sMap.put(t, value);
    }

    /** Returns the element that (s,t) is mapped to.*/
    public V get(T s, U t) {
        LinkedHashMap<U,V> sMap = this.map.get(s);
        if (sMap != null) {
            return sMap.get(t);
        }
        return null;
    }

    public Set<T> keySet() {
        return this.map.keySet();
    }

    public Map<U,V> get(T key) {
        return this.map.get(key);
    }

}
