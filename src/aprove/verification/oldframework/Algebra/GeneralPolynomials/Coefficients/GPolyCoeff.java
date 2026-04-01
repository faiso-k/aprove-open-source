/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import aprove.prooftree.Export.Utility.*;
import immutables.*;

/**
 * A coefficient for general polynomials must be immutable so that the
 * polynomials itself are immutable. Furthermore they must be exportable,
 * because orders using general polynomials may be exportable.
 * @author cotto
 */
public interface GPolyCoeff extends Immutable, Exportable {

}
