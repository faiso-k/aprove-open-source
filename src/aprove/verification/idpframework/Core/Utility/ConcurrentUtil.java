package aprove.verification.idpframework.Core.Utility;

import java.util.concurrent.*;

/**
 *
 * @author MP
 */
public class ConcurrentUtil {

    public static <K, V> V addToCache(final ConcurrentMap<K, V> cache,
        final K key,
        final V value) {
        V res = cache.get(key);
        if (res != null) {
            return res;
        }

        res = cache.putIfAbsent(key, value);
        if (res == null) {
            return value;
        } else {
            return res;
        }
    }

}

