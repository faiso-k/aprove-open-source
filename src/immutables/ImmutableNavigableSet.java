package immutables;

import java.util.*;

/**
 * All classes of immutable data structures whose corresponding mutable data structures implement NavigableSet<E> 
 * should implement ImmutableNavigableSet<E>.
 * @author cryingshadow
 * @version $Id$
 * @param <E> The type of elements in this set.
 */
public interface ImmutableNavigableSet<E> extends NavigableSet<E>, ImmutableSortedSet<E> {

}
