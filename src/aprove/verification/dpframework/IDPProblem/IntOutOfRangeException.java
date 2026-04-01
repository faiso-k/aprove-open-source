/**
 *
 * @author noschinski
 * @version $Id$
 */

/**
 *
 */
package aprove.verification.dpframework.IDPProblem;

import java.math.*;

public class IntOutOfRangeException extends Exception {

    private static final long serialVersionUID = -6385388646569272289L;

    /**
     * The value being out-of-range.
     */
    private BigInteger offending;

    /**
     * The limit which was violated.
     */
    private BigInteger limit;

    /**
     * <code>number</code> violated limit <code>limit</code>.
     */
    public IntOutOfRangeException(int number, int limit) {
        this(BigInteger.valueOf(number), BigInteger.valueOf(limit));
    }

    /**
     * <code>number</code> violated limit <code>limit</code>.
     */
    public IntOutOfRangeException(BigInteger number, BigInteger limit) {
        this.offending = number;
        this.limit = limit;
    }

    public BigInteger getLimit() {
        return this.limit;
    }

    public BigInteger getOffending() {
        return this.offending;
    }
}