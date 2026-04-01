/**
 * @author Carsten Otto
 * @version $Id$
 */
package aprove.verification.oldframework.Algebra;

/**
 * Classes implementing this interface provide ring operations (+, *) where
 * (E, +) is an abelian group.
 * @param <E> The type of ring elements.
 */
public interface Ring<E> extends Semiring<E> {
    /**
     * Subtraction. This must be possible because E contains the inverse element
     * regarding +.
     * @param minuend The minuend.
     * @param subtrahend The subtrahend.
     * @return The difference minuend - subtrahend.
     */
    E minus(E minuend, E subtrahend);

    /**
     * Get the inverse element of E wrt. "+".
     * @param target The inverse of this element is the result.
     * @return the inverse element of target.
     */
    E getInverse(E target);

    /**
     * Supplies a default implementation for isRing().
     */
    public abstract class RingSkeleton<E> implements Ring<E> {

        @Override
        public boolean isRing() {
            return true;
        }
    }
}
