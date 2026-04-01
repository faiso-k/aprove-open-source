package immutables;

import java.util.*;

/**
 * All immutable data structures whose corresponding mutable data structures
 * implement Map<K,V> should implement ImmutableMap<K,V>.
 *
 * @author Carsten Fuhs
 * @version $Id$
 * @param <K> The type of the map's keys.
 * @param <V> The type of the map's values.
 */
public interface ImmutableMap<K,V> extends Map<K,V>, Immutable {
}
