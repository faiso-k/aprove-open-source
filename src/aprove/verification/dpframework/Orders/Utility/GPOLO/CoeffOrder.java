/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

/**
 * A CoeffOrder must give information about the relation of any given
 * coefficient to 0, or another coefficient.
 * @author cotto
 * @param <C> The type of the coefficient.
 */
public interface CoeffOrder<C> {
    /**
     * @param object The object to compare with 0.
     * @return a value &lt; 0 for any value smaller than 0, 0 for the 0 element,
     * a value &gt; 0 for any value greater than 0.
     */
    int signum(C object);

    /**
     * @param first
     * @param second
     * @return true if both coefficients are equal
     */
    boolean equal(C first, C second);

    /**
     * @param first
     * @param second
     * @return true if the first coefficient is strictly greater than the second.
     * Note that "strictly greater" need not always be defined in the intuitive way.
     */
    boolean isGreater(C first, C second);

    /**
     * @param first
     * @param second
     * @return true if the first coefficient is weakly greater than the second.
     * Note that this order does not have to be the reflexive closure of the one
     * represented by isGreater().
     */
    boolean isGreaterOrEqual(C first, C second);
}
