/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import immutables.*;

/**
 * A ConcatNode represents the concatenation of a coefficient and a
 * corresponding variable part. The monomial 3b o x is a concatenation of 3b and
 * x. Because a ConcatNode includes both a coefficient and a variable part it is
 * a valid GPoly.
 * @version $Id$
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public class ConcatNode<C extends GPolyCoeff, V extends GPolyVar> extends GPoly.GPolySkeleton<C, V> {
    /**
     * The coefficient.
     */
    private final C coeff;

    /**
     * Set list containing all coefficients (here only one).
     */
    private ImmutableList<C> coeffs;

    /**
     * The variable part node.
     */
    private final VarPartNode<V> var;

    /**
     * Create a ConcatNode which concatenates a coefficient node and a variable
     * part node.
     * @param coeffParam The coefficient of the resulting monomial.
     * @param varParam The variable part node holding the variable part of the
     * resulting monomial.
     */
    ConcatNode(final C coeffParam, final VarPartNode<V> varParam) {
        this.coeff = coeffParam;
        this.var = varParam;
        assert (varParam != null);
    }

    /**
     * @return true iff this node contains some variable.
     */
    @Override
    public boolean containsVariable() {
        return this.var.containsVariable();
    }

    /**
     * @return the set of all variables contained below this node.
     */
    @Override
    public ImmutableSet<V> getVariables() {
        return this.var.getVariables();
    }

    /**
     * @return the map of all variables contained below this node to the number
     * of their occurrences in that node (i.e., their exponents).
     */
    public ImmutableMap<V, Integer> getVariablesWithExponents() {
        return this.var.getVariablesWithExponents();
    }

    /**
     * Return and create (if necessary) the set containing the coefficient.
     * @return the set containing the coefficient.
     */
    @Override
    public synchronized ImmutableList<C> getCoeffs() {
        if (this.coeffs == null) {
            final List<C> list = new ArrayList<>(1);
            list.add(this.coeff);
            this.coeffs = ImmutableCreator.create(list);
        }
        return this.coeffs;
    }

    /**
     * @return the list of all coefficients occurring in
     * this polynomial as a coefficient for a variable part containing the given
     * variable.
     * @param varParam Extract the coefficients that belong to some variable
     * part containing this variable.
     */
    @Override
    public ImmutableList<C> getCoeffs(final V varParam) {
        if (this.var.containsVariable(varParam)) {
            final List<C> list = new ArrayList<>(1);
            list.add(this.coeff);
            return ImmutableCreator.create(list);
        } else {
            return ImmutableCreator.create(Collections.<C>emptyList());
        }
    }

    /**
     * @param eu Some export util.
     * @return some readable string representation.
     */
    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        String coeffString = "";
        String varString = "";
        if (this.coeff != null) {
            coeffString = this.coeff.export(eu);
        } else {
            coeffString = "[1]";
        }
        varString = this.var.export(eu);
        if (varString.length() != 0 && "[1]".equals(coeffString)) {
            // 1*x is x.
            coeffString = "";
        }
        if (coeffString.length() != 0 && "[1]".equals(varString)) {
            // x*1 is x.
            varString = "";
        }
        sb.append(coeffString);
        sb.append(varString);
        return sb.toString();
    }

    /**
     * @return the coefficient.
     */
    public C getCoeff() {
        return this.coeff;
    }

    /**
     * @return the varpart node.
     */
    public VarPartNode<V> getVarPartNode() {
        return this.var;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isOne() {
        return this.coeff == null && this.var.isOne();
    }

    /**
     * Feed this node to the visitor.
     * @param gpv The visitor visiting this node.
     * @return Some GPoly defined by the visitor.
     */
    @Override
    public GPoly<C, V> visit(final GPolyVisitor<C, V> gpv) {
        gpv.fcaseConcatNode(this);
        return gpv.caseConcatNode(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean hasMaxMin() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public C computeConstant(final Semiring<C> ring) {
        if (this.var.isOne()) {
            if (this.coeff == null) {
                return ring.one();
            }
            return this.coeff;
        }
        return null;
    }
}
