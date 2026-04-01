package aprove.verification.oldframework.Utility.GenericStructures;

/**
 * Combines three objects (the two arguments and the connector) to a new one.
 * @author cryingshadow
 * @version $Id$
 * @param <A> The type of the first argument.
 * @param <B> The type of the second argument.
 * @param <C> The type of the connector.
 * @param <R> The result type.
 */
public interface Combinator<A, B, C, R> {

    /**
     * @param connector The connecting object.
     * @param lhs The first argument.
     * @param rhs The second argument.
     * @return The resulting object.
     */
    R combine(C connector, A lhs, B rhs);

}
