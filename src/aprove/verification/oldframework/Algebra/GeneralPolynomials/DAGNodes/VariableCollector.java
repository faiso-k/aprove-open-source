/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import aprove.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;

/**
 * Multiply all variables found under the given starting node. Use the given
 * monoid for that.
 * @author cotto
 * @version $Id$
 *
 * @param <V> The type of the variables.
 */
public class VariableCollector<V extends GPolyVar> extends VarPartNodeVisitor<V> {
    /**
     * The resulting GMonomial.
     */
    private GMonomial<V> result;

    /**
     * This monoid is used to multiply two monomials.
     */
    private CMonoid<GMonomial<V>> monoid;

    /**
     * @param monoidParam This monoid is used to multiply two monomials.
     */
    public VariableCollector(final CMonoid<GMonomial<V>> monoidParam) {
        this.monoid = monoidParam;
        this.result = monoidParam.neutral();
    }

    /**
     * Multiply every single variable to the result using the given monoid.
     * @param v The current variablepart node.
     * @param left The left child.
     * @param right The right child.
     * @return v itself.
     */
    @Override
    public VarPartNode<V> caseVarPartNode(
            final VarPartNode<V> v,
            final VarPartNode<V> left,
            final VarPartNode<V> right) {
        GMonomial<V> mon;
        if (v.hasMonomial(this.monoid)) {
            // already computed
            mon = v.getMonomial(this.monoid);
            this.result = this.monoid.op(this.result, mon);
        } else {
            // not yet computed
            V var = v.getVar();
            if (var != null) {
                mon = new GMonomial<V>(var);
                v.putMonomial(this.monoid, mon);
                this.result = this.monoid.op(this.result, mon);
            } else if (!v.isLeaf()) {
                // be nice and fill the node with the monomial information,
                // which is unneeded here
                if (Globals.useAssertions) {
                    assert (v.getLeft() != null
                            && v.getLeft().getMonomial(this.monoid) != null);
                    assert (v.getRight() != null
                            && v.getRight().getMonomial(this.monoid) != null);
                }
                v.putMonomial(this.monoid, this.monoid.op(
                        v.getLeft().getMonomial(this.monoid),
                        v.getRight().getMonomial(this.monoid)));
            } else {
                v.putMonomial(this.monoid, this.monoid.neutral());
            }
        }
        return v;
    }

    /**
     * @return the result, which is a GMonomial.
     */
    public GMonomial<V> getMonomial() {
        return this.result;
    }
}
