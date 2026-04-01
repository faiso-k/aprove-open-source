/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

/**
 *  Classes implementing this interface can be represented as a SMTLIB formula
 */
public interface SMTLIBFormatter {

    /**
     *  Gives a representation as an SMTLIB formula
     */
    public String toSMTLIB();

}
