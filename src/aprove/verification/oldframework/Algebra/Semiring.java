package aprove.verification.oldframework.Algebra;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;

/**
 * Classes implementing this interface provide semiring operations (+, *).
 * Unlike with actual rings, the existence of an additive inverse (and thus, a
 * minus operation) is not assumed.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public interface Semiring<E> {

    /**
     * Addition, commutative.
     * @param first The first addend.
     * @param second The second addend.
     * @return The sum first + second.
     */
    E plus(E first, E second);

    /**
     * Multiplication, associative.
     * @param first The first factor.
     * @param second The second factor.
     * @return The product first * second (not necessarily second * first!).
     */
    E times(E first, E second);

    /**
     * @return the neutral element wrt. addition.
     */
    E zero();

    /**
     * @return the neutral element wrt. multiplication.
     * @return
     */
    E one();

    /**
     * @return true if the structure is an actual ring, false otherwise
     */
    boolean isRing();

    SpecializedGInterpretation getSpecializedGInterpretation();

    /**
     * Supplies a default implementation for isRing().
     */
    public abstract class SemiringSkeleton<E> implements Semiring<E> {

        @Override
        public boolean isRing() {
            return false;
        }
    }
}