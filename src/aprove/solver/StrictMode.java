/**
 * @author cotto
 * @version $Id$
 */

package aprove.solver;

/**
 * The strict modes currently supported (at least by some orders).
 * @author cotto
 */
public enum StrictMode {
    /**
     * All pairs have to be strict.
     */
    ALLSTRICT,
    /**
     * At least one pair must be oriented strictly.
     * Introduces new variables (si):
     * pair1 - s1 >= 0
     * ...
     * pairn - sn >= 0
     * s1 + ... + sn > 0
     */
    AUTOSTRICT,
    /**
     * At least one pair must be oriented strictly.
     * Introduces no new variables:
     * coeff1(pair1) >= 0
     * ...
     * coeffn(pair1) >= 0
     * ...
     * coeff1(pairn) >= 0
     * ...
     * coeffn(pairn) >= 0
     * const(pair1) + ... + const(pairn) > 0
     */
    AUTOSTRICTJAR,
    /**
     * At least one pair must be oriented strictly.
     * Introduces no new variables.
     * pair1 >= 0
     * ...
     * pairn >= 0
     * "and not all constant parts do not differ":
     * NOT(AND(const(l) - const(r) = 0))
     */
    SEARCHSTRICT
}
