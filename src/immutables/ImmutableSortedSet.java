package immutables;

import java.util.*;

/**
 * All classes of immutable data structures whose corresponding mutable data structures implement SortedSet<E> should 
 * implement ImmutableSortedSet<E>.
 * @author cryingshadow
 * @version $Id$
 * @param <E> The type of elements in this set.
 */
public interface ImmutableSortedSet<E> extends SortedSet<E>, ImmutableSet<E> {

}
