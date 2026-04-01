package aprove.verification.oldframework.BasicStructures;

/**
 * Object visitable by a Visitor.
 * @author cryingshadow
 * @version $Id$
 * @param <V> The type of the visited objects.
 * @param <R> The type of the resulting objects.
 */
public interface Visitable<V, R> {

    /**
     * @param v A visitor.
     * @return The resulting object when applying the specified visitor depth-first (so all reachable objects before
     *         their origin).
     */
    R accept(Visitor<V, R> v);

}
