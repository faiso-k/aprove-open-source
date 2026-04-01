/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class MinNode<C extends GPolyCoeff, V extends GPolyVar> extends BinaryNode<C, V> {
    /**
     * Create a MinusNode which connects the two given Polynomials.
     * @param leftParam The minuend.
     * @param rightParam The subtrahend.
     */
    MinNode(final GPoly<C, V> leftParam, final GPoly<C, V> rightParam) {
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
        final StringBuilder sb = new StringBuilder("min{");
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
        gpv.fcaseMinNode(this);
        GPoly<C, V> newLeft = null;
        GPoly<C, V> newRight = null;
        if (this.getLeft() != null) {
            newLeft = gpv.applyTo(this.getLeft());
        }
        if (this.getRight() != null) {
            newRight = gpv.applyTo(this.getRight());
        }
        return gpv.caseMinNode(this, newLeft, newRight);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isFlat(final Semiring<C> ringC, final CMonoid<GMonomial<V>> monoid) {
        final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair = new Pair<>(ringC, monoid);
        return this.left.isFlat(pair) && this.right.isFlat(pair);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableMap<GMonomial<V>, C> getMonomials(final Semiring<C> ringC, final CMonoid<GMonomial<V>> monoid) {
        throw new UnsupportedOperationException("min nodes can not be represented as monomials");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableMap<GMonomial<V>, C> getMonomials(final Pair<Semiring<C>, CMonoid<GMonomial<V>>> pair) {
        throw new UnsupportedOperationException("min nodes can not be represented as monomials");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Map<Pair<Semiring<C>, CMonoid<GMonomial<V>>>, ImmutableMap<GMonomial<V>, C>> getMonomials() {
        throw new UnsupportedOperationException("min nodes can not be represented as monomials");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean hasMaxMin() {
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public C computeConstant(final Semiring<C> ring) {
        return null;
    }
}
