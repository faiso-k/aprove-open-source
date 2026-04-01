package immutables;

import java.util.*;

/**
 * All classes of immutable data structures whose corresponding mutable
 * data structures implement Set<E> should implement ImmutableSet<E>.
 *
 * @author Carsten Fuhs
 * @version $Id$
 * @param <E> The type of elements in this set.
 */
public interface ImmutableSet<E> extends Set<E>, ImmutableCollection<E> {

}
