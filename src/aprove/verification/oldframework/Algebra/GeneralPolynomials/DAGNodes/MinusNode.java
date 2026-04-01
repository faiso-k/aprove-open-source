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
 * A MinusNode represents the difference of two GPolys. Before the result is
 * calculated the information about the resulting polynomial is hidden in the
 * left and right children (minuend and subtrahend).
 * @version $Id$
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public class MinusNode<C extends GPolyCoeff, V extends GPolyVar> extends BinaryNode<C, V> {
    /**
     * Create a MinusNode which connects the two given Polynomials.
     * @param leftParam The minuend.
     * @param rightParam The subtrahend.
     */
    MinusNode(final GPoly<C, V> leftParam, final GPoly<C, V> rightParam) {
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
        final StringBuilder sb = new StringBuilder("-{");
        sb.append(this.getLeft().export(eu));
        sb.append(", ");
        sb.append(this.getRight().export(eu));
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
        gpv.fcaseMinusNode(this);
        GPoly<C, V> newLeft = null;
        GPoly<C, V> newRight = null;
        if (this.getLeft() != null) {
            newLeft = gpv.applyTo(this.getLeft());
        }
        if (this.getRight() != null) {
            newRight = gpv.applyTo(this.getRight());
        }
        return gpv.caseMinusNode(this, newLeft, newRight);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isZero() {
        return this.left.equals(this.right);
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
                assert (ring.isRing());
                final Ring<C> realRing = (Ring<C>) ring;
                return realRing.minus(constantLeft, constantRight);
            }
        }
        return null;
    }
}
