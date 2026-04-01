/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.SMT_LIA;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * @author noschinski
 *
 * Provides an linear integer arithmetic constraint, i.e. a tuple of
 * two linear polynomials and a relation.
 *
 */
public class LIAConstraint {
    private final GPoly<BigIntImmutable, GPolyVar> left;
    private final GPoly<BigIntImmutable, GPolyVar> right;
    private final ArithmeticRelation relation;

    public LIAConstraint(
            GPoly<BigIntImmutable, GPolyVar> left,
            GPoly<BigIntImmutable, GPolyVar> right,
            ArithmeticRelation relation) {
        this.left = left;
        this.right = right;
        this.relation = relation;
    }

    /**
     * Returns the left polynomial of the constraint.
     */
    public GPoly<BigIntImmutable, GPolyVar> getLeft() {
        return this.left;
    }

    /**
     * Returns the relation symbol of the constraint.
     */
    public ArithmeticRelation getRelation() {
        return this.relation;
    }

    /**
     * Returns the right symbol of the constranit.
     */
    public GPoly<BigIntImmutable, GPolyVar> getRight() {
        return this.right;
    }

}
