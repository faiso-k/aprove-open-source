package aprove.verification.oldframework.BasicStructures;

/**
 * Visitor.
 * @author cryingshadow
 * @version $Id$
 * @param <V> The type of the visited objects.
 * @param <R> The type of the resulting objects.
 */
public interface Visitor<V, R> {

    /**
     * @param v The visited object.
     * @return The resulting object.
     */
    R visit(V v);

}
