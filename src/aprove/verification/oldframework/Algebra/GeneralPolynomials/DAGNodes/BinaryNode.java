/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import immutables.*;

/**
 * This abstract class provides basic methods for binary DAG nodes containing
 * two GPolys as children.
 * @author cotto
 * @version $Id$
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public abstract class BinaryNode<C extends GPolyCoeff, V extends GPolyVar> extends GPoly.GPolySkeleton<C, V> {
    /**
     * The left child.
     */
    protected final GPoly<C, V> left;

    /**
     * The right child.
     */
    protected final GPoly<C, V> right;

    /**
     * The set of all variables contained below this node.
     */
    private ImmutableSet<V> variables;

    /**
     * The list of all coeffs contained below this node.
     */
    private ImmutableList<C> coeffs;

    /**
     * Set the left and right child.
     * @param leftParam The left child.
     * @param rightParam The right child.
     */
    public BinaryNode(final GPoly<C, V> leftParam, final GPoly<C, V> rightParam) {
        assert (leftParam != null);
        assert (rightParam != null);
        this.left = leftParam;
        this.right = rightParam;
    }

    /**
     * @return true iff this node contains some variable.
     */
    @Override
    public boolean containsVariable() {
        return this.left.containsVariable() || this.right.containsVariable();
    }

    /**
     * @return the left child.
     */
    public GPoly<C, V> getLeft() {
        return this.left;
    }

    /**
     * @return the right child.
     */
    public GPoly<C, V> getRight() {
        return this.right;
    }

    /**
     * @return the set of all variables contained below this node.
     */
    @Override
    public synchronized ImmutableSet<V> getVariables() {
        if (this.variables == null) {
            this.calculateVariables();
        }
        return this.variables;
    }

    /**
     * Calculate the set of all variables below this node.
     */
    private synchronized void calculateVariables() {
        if (Globals.useAssertions) {
            assert (this.variables == null);
        }
        final Set<V> temp = new LinkedHashSet<>(this.left.getVariables());
        temp.addAll(this.right.getVariables());
        this.variables = ImmutableCreator.create(temp);
    }

    /**
     * @return the set of all coeffs contained below this node.
     */
    @Override
    public synchronized ImmutableList<C> getCoeffs() {
        if (this.coeffs == null) {
            this.calculateCoeffs();
        }
        return this.coeffs;
    }

    /**
     * @return the list of all coefficients (which are polynomials!) occurring
     * in this polynomial as a coefficient for a variable part containing the
     * given variable.
     * @param varParam Extract the coefficients that belong to some variable
     * part containing this variable.
     */
    @Override
    public ImmutableList<C> getCoeffs(final V varParam) {
        final ImmutableSet<V> leftVars = this.left.getVariables();
        final ImmutableSet<V> rightVars = this.right.getVariables();
        final List<C> result = new ArrayList<>();
        if (leftVars.contains(varParam)) {
            result.addAll(this.left.getCoeffs(varParam));
        }
        if (rightVars.contains(varParam)) {
            result.addAll(this.right.getCoeffs(varParam));
        }
        return ImmutableCreator.create(result);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean hasMaxMin() {
        return this.left.hasMaxMin() || this.right.hasMaxMin();
    }

    /**
     * Calculate the set of all coeffs below this node.
     */
    private synchronized void calculateCoeffs() {
        if (Globals.useAssertions) {
            assert (this.coeffs == null);
        }
        final List<C> temp = new ArrayList<>(this.left.getCoeffs());
        temp.addAll(this.right.getCoeffs());
        this.coeffs = ImmutableCreator.create(temp);
    }
}
