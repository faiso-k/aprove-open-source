/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Every class implementing this interface (which should be all the DAG nodes
 * defining a proper GPoly) can be visited by some GPolyVisitor.
 * @author cotto
 * @version $Id$
 *
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public interface VisitableGPoly<C extends GPolyCoeff, V extends GPolyVar> {
    /**
     * When the visitor calls this method, the implementation feeds itself and
     * all children into the visitor. This happens depending on the current
     * type, e.g. in the case of a PlusNode after visit(visitor) is called the
     * class will call visitor.casePlusNode.
     * @param gpv The visitor doing the work.
     * @return A node that is the result of the visit. The result is defined
     * by the visitor. One example might be the substituted polynomial when a
     * substitution visitor is used.
     */
    GPoly<C, V> visit(GPolyVisitor<C, V> gpv);
}
