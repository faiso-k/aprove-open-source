/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This visitor visits every GPoly node in the graph and replaces every
 * occurrence of the given variable by the given polynomial.
 * @author cotto
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public class VarSubstitutionVisitor<C extends GPolyCoeff, V extends GPolyVar> extends GPolyVisitor<C, V> {
    /**
     * The key variable should be replaced with the value poly.
     */
    private final Map<V, ? extends GPoly<C, V>> replacement;

    /**
     * New nodes will be created using this factory.
     */
    private final GPolyFactory<C, V> factory;

    /**
     * This ring is used to improve the substitution of certain nodes
     * by a) recognizing ones and zeros and b) doing math on coeffs. May be null.
     */
    private final Semiring<C> ringC;

    /**
     * Replace the given variables by the given polynomials.
     * @param replacementParam The replacements for the given variables.
     * @param factoryParam This factory will be used to create new nodes.
     * @param ringCParam this ring will be used for optimizations, may be null.
     */
    public VarSubstitutionVisitor(final Map<V, ? extends GPoly<C, V>> replacementParam,
            final GPolyFactory<C, V> factoryParam, final Semiring<C> ringCParam) {
        this.replacement = replacementParam;
        this.factory = factoryParam;
        this.ringC = ringCParam;
    }

    /**
     * Replace the variables in both children and return the new times node.
     * @param t The TimesNode being visited.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return The new TimesNode where the variables are substituted.
     */
    @Override
    public GPoly<C, V> caseTimesNode(final TimesNode<C, V> t, final GPoly<C, V> left, final GPoly<C, V> right) {
        final Pair<GPoly<C, V>, GPoly<C, V>> pair = this.computeConstants(left, right);
        return this.factory.times(pair.x, pair.y);
    }

    /**
     * Replace the variables in both children and return the new plus node.
     * @param p The PlusNode being visited.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return The new PlusNode where the variable are substituted.
     */
    @Override
    public GPoly<C, V> casePlusNode(final PlusNode<C, V> p, final GPoly<C, V> left, final GPoly<C, V> right) {
        final Pair<GPoly<C, V>, GPoly<C, V>> pair = this.computeConstants(left, right);
        return this.factory.plus(pair.x, pair.y);
    }

    /**
     * Replace the variables in both children and return the new minus node.
     * @param m The MinusNode being visited.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return The new MinusNode where the variable are substituted.
     */
    @Override
    public GPoly<C, V> caseMinusNode(final MinusNode<C, V> m, final GPoly<C, V> left, final GPoly<C, V> right) {
        final Pair<GPoly<C, V>, GPoly<C, V>> pair = this.computeConstants(left, right);
        return this.factory.minus(pair.x, pair.y);
    }

    /**
     * Replace the variables in both children and return the new max node.
     * @param m The MaxNode being visited.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return The new MaxNode where the variable are substituted.
     */
    @Override
    public GPoly<C, V> caseMaxNode(final MaxNode<C, V> m, final GPoly<C, V> left, final GPoly<C, V> right) {
        if (m.getLeft() == left && m.getRight() == right) {
            return m;
        } else {
            return this.factory.max(left, right);
        }
    }

    /**
     * Replace the variables in both children and return the new min node.
     * @param m The MinNode being visited.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return The new MinNode where the variable are substituted.
     */
    @Override
    public GPoly<C, V> caseMinNode(final MinNode<C, V> m, final GPoly<C, V> left, final GPoly<C, V> right) {
        if (m.getLeft() == left && m.getRight() == right) {
            return m;
        } else {
            return this.factory.min(left, right);
        }
    }

    // avoid runtime exceptions

    /**
     * {@inheritDoc}
     */
    @Override
    public void fcaseMaxNode(final MaxNode<C, V> m) {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void fcaseMinNode(final MinNode<C, V> m) {
    }

    /**
     * Determine if this node has to be changed, when the variable to be
     * replaced appears in the variable part. If so, this node and its children
     * will be redesigned to allow the variable to be substituted (it is not
     * allowed to attach a proper polynomial under a concatnode).
     * @param c The ConcatNode being visited.
     * @return Some new node where the variable is substituted.
     */
    @Override
    public GPoly<C, V> caseConcatNode(final ConcatNode<C, V> c) {
        if (c.getVarPartNode() == null) {
            // this node is (and stays) the 1 element of any ring
            return c;
        }
        final Set<V> vars = new LinkedHashSet<>(c.getVarPartNode().getVariables());
        final Set<V> affected = new LinkedHashSet<>();
        for (final V var : vars) {
            if (var.isAffected(this.replacement.keySet())) {
                affected.add(var);
            }
        }

        if (affected.size() > 0) {
            /*
             * Alter the current variable part so that all occurrences of the
             * variables are replaced by 1.
             * Then multiply the replacement polynomials (from right) as often
             * as the corresponding variable was removed.
             */

            // replace every occurrence of the variable by 1
            final VariableReplacer<V> vr = new VariableReplacer<>(affected, this.factory.getVarOne(), this.factory);
            final VarPartNode<V> newVarPartNode = vr.applyTo(c.getVarPartNode());

            /*
             * If we only substitute variables by constants (as when specializing an interpretation), do the math
             * directly in order to prevent introduction of superfluous TimesNodes (and thus harming the visual
             * representation's readability).
             *
             * Obviously this requires that the visitor knows how to do the math in the first place, so setting the
             * coefficient ring is necessary for this.
             */
            OPTIMIZATION: if (this.ringC != null) {
                for (final V var : affected) {
                    if (!this.replacement.get(var).isConstant()) {
                        break OPTIMIZATION;
                    }
                }

                C res = this.ringC.one();
                for (final V var : affected) {
                    final BigInteger exponent = vr.getNumbers().get(var);
                    assert (exponent.signum() > 0);

                    final GPoly<C, V> poly = this.replacement.get(var);
                    assert (poly.isConstant());
                    final C constant = poly.computeConstant(this.ringC);
                    if (constant == null) {
                        break OPTIMIZATION;
                    }

                    // apply the exponent
                    BigInteger remaining = exponent;
                    while (remaining.signum() > 0) {
                        res = this.ringC.times(constant, res);
                        remaining = remaining.subtract(BigInteger.ONE);
                    }
                }

                // also consider the old coefficient of c = factor*x
                final C factor = c.getCoeff();
                if (factor != null) {
                    res = this.ringC.times(res, factor);
                }
                if (this.ringC.zero().equals(res)) {
                    return this.factory.zero();
                }
                if (newVarPartNode.isOne() && this.ringC.one().equals(res)) {
                    return this.factory.one();
                }
                return this.factory.concat(res, newVarPartNode);
            }

            // this new concat node will not be the final result, because
            // the replacement is missing completely.
            final GPoly<C, V> newConcatNode = this.factory.concat(c.getCoeff(), newVarPartNode);

            // build the replacement node which is pol1^exp1 * pols2^exp2 * ...
            GPoly<C, V> replacementNode = newConcatNode;
            for (final Map.Entry<V, BigInteger> entry : vr.getNumbers().entrySet()) {
                final V var = entry.getKey();
                final BigInteger exponent = entry.getValue();
                if (Globals.useAssertions) {
                    assert (exponent.compareTo(BigInteger.ZERO) > 0) : "No variable was found, but this branch is executed?";
                }
                final GPoly<C, V> newPoly = var.replace(this.replacement);
                replacementNode = this.factory.times(replacementNode, this.factory.power(newPoly, exponent));
            }
            // combine the new concat node (still holding the unchanged
            // coefficient and the variables that were not replaced) with the
            // replacement
            return replacementNode;
        } else {
            // nothing to do here, the variable was not found
            return c;
        }
    }

    /**
     * If any of the two polynomials represents a constant, replace the (complicated?) object by a simple object for the
     * constant. If the represented constant is 1 or 0, the factory may use this information to optimize when working with the returned polynomials.
     * @param polyOne a polynomial
     * @param polyTwo another polynomial
     * @return a pair of polynomials where the input polynomials may have been changed to a simpler representation
     */
    private Pair<GPoly<C, V>, GPoly<C, V>> computeConstants(final GPoly<C, V> polyOne, final GPoly<C, V> polyTwo) {
        GPoly<C, V> newLeft = polyOne;
        GPoly<C, V> newRight = polyTwo;
        if (this.ringC != null) {
            if (polyOne.isConstant()) {
                final C constant = polyOne.computeConstant(this.ringC);
                if (constant != null) {
                    if (this.ringC.one().equals(constant)) {
                        newLeft = this.factory.one();
                    }
                    if (this.ringC.zero().equals(constant)) {
                        newLeft = this.factory.zero();
                    } else {
                        newLeft = this.factory.buildFromCoeff(constant);
                    }
                }
            }
            if (polyTwo.isConstant()) {
                final C constant = polyTwo.computeConstant(this.ringC);
                if (constant != null) {
                    if (this.ringC.one().equals(constant)) {
                        newRight = this.factory.one();
                    }
                    if (this.ringC.zero().equals(constant)) {
                        newRight = this.factory.zero();
                    } else {
                        newRight = this.factory.buildFromCoeff(constant);
                    }
                }
            }
        }
        return new Pair<>(newLeft, newRight);
    }
}
