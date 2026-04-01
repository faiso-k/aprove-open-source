/**
 * @author Carsten Otto
 * @version $Id$
 */
package aprove.verification.oldframework.Algebra;

/**
 * Classes implementing this interface provide an operation op such that (E, op)
 * is a commutative monoid.
 * @param <E> The type of monoid elements.
 */
public interface CMonoid<E> {
    /**
     * Some commutative operation, such that (E, op) is a commutative monoid.
     * @param first The first argument.
     * @param second The second argument.
     * @return The operation first op second.
     */
    E op(E first, E second);

    /**
     * @return the neutral element wrt. op.
     */
    E neutral();
}
