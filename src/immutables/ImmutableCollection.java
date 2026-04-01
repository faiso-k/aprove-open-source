package immutables;

import java.util.*;

/**
 * All interfaces for immutable data structures whose corresponding
 * non-immutable interfaces extend java.util.Collection<T> should extend
 * ImmutableCollection<T>, either directly or indirectly.
 *
 * @author Carsten Fuhs
 * @version $Id$
 * @param <T> The type of the collection's elements.
 */
public interface ImmutableCollection<T> extends Collection<T>, Immutable {

}
