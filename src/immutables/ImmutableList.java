package immutables;

import java.util.*;

/**
 * All immutable data structures whose corresponding mutable data structures
 * implement List<T> should implement ImmutableList<T>.
 *
 * @author Carsten Fuhs
 * @version $Id$
 * @param <T> The type of the list elements.
 */
public interface ImmutableList<T> extends List<T>, ImmutableCollection<T> {

}
