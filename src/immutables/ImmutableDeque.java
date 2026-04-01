package immutables;

import java.util.*;

/**
 * All immutable data structures whose corresponding mutable data structures implement Deque<T> should implement 
 * ImmutableDeque<T>.
 * @author cryingshadow
 * @version $Id$
 * @param <T> The type of the Deque's elements.
 */
public interface ImmutableDeque<T> extends Deque<T>, ImmutableCollection<T> {
}
