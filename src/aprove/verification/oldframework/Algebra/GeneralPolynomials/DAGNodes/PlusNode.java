/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;

/**
 * A PlusNode represents the sum of two GPolys. Before the result is calculated
 * the information about the resulting polynomial is hidden in the left and
 * right children (addends).
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public class PlusNode<C extends GPolyCoeff, V extends GPolyVar> extends BinaryNode<C, V> {
    /**
     * Create a PlusNode which connects the two given Polynomials.
     * @param leftParam The first addend.
     * @param rightParam The second addend.
     */
    PlusNode(final GPoly<C, V> leftParam, final GPoly<C, V> rightParam) {
        super(leftParam, rightParam);
        if (Globals.useAssertions) {
            assert (leftParam != null);
            assert (rightParam != null);
        }
    }

    /**
     * @param eu some export util.
     * @return some readable string representation.
     */
    @Override
    public String export(final Export_Util eu) {
        final String leftString = this.getLeft().export(eu);
        final String rightString = this.getRight().export(eu);
        final StringBuilder sb = new StringBuilder("+{");
        sb.append(leftString);
        sb.append(", ");
        sb.append(rightString);
        sb.append("}");
        return sb.toString();
    }

    /**
     * Visit this node and the two children.
     * @param gpv The visitor visiting this node.
     * @return some visitable object defined by the visitor.
     */
    @Override
    public GPoly<C, V> visit(final GPolyVisitor<C, V> gpv) {
        gpv.fcasePlusNode(this);
        GPoly<C, V> newLeft = null;
        GPoly<C, V> newRight = null;
        if (this.getLeft() != null) {
            newLeft = gpv.applyTo(this.getLeft());
        }
        if (this.getRight() != null) {
            newRight = gpv.applyTo(this.getRight());
        }
        return gpv.casePlusNode(this, newLeft, newRight);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public C computeConstant(final Semiring<C> ring) {
        final C constantLeft = this.left.computeConstant(ring);
        if (constantLeft != null) {
            final C constantRight = this.right.computeConstant(ring);
            if (constantRight != null) {
                return ring.plus(constantLeft, constantRight);
            }
        }
        return null;
    }
}
