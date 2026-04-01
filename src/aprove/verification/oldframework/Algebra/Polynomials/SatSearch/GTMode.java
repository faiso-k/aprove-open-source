package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

/**
 * What way is GT (">") supposed to be encoded?
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public enum GTMode {
    DEEP, // Codish LPO style, depth O(n)
    FLAT, // "classical" flat style, depth O(1)
    LPO_LIKE // similar to LPO implementation of GT
             // as of 10/2006
}