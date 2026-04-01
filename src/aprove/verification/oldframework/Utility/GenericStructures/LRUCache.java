package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

public class LRUCache<K, V> extends LinkedHashMap<K, V> {

    private static final long serialVersionUID = 1L;
    private static final float loadFactor = 0.75f;

    private int limit;

    public LRUCache(int limit) {
        super((int) Math.ceil(limit/LRUCache.loadFactor)+1, LRUCache.loadFactor, true);
        this.limit = limit;
    }

    @Override
    protected boolean removeEldestEntry(Map.Entry<K, V> entry) {
        return this.size() > this.limit;
    }

}
