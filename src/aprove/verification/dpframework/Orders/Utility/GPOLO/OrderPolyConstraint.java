/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import immutables.*;

/**
 * A OrderPolyConstraint is a constraint where the atoms are OrderPolys with
 * some relation, e.g. 3ax^2 + by >= 0. Extensions over these atoms are
 * quantifiers (to give atoms with variables some meaning) and boolean
 * operators.
 *
 * For pretty printing order poly constraints, see {@link OPCExportVisitor}.
 * @author cotto
 * @param <C> The type of the coefficients (deep) inside the OrderPolys.
 */
public interface OrderPolyConstraint<C extends GPolyCoeff>
    extends VisitableConstraint<C>, Immutable {
    /**
     * @return true iff the constraint does not contain a free variable.
     */
    boolean isClosed();

    /**
     * @return all variables that are not bound by some quantifier.
     */
    Set<GPolyVar> getFreeVariables();

}
