/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This visitor visits every GPoly node in the graph and replaces every
 * occurrence of the given coeff by the given polynomial.
 * @author cotto
 * @version $Id$
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public class CoeffSubstitutionVisitor<C extends GPolyCoeff, V extends GPolyVar> extends GPolyVisitor<C, V> {
    /**
     * The coeff to be replaced.
     */
    private final C coeff;

    /**
     * The coeff to replace the coeff.
     */
    private final C replacement;

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
     * Replace the given coeff by the given substitute.
     * @param coeffParam The coeff to be replaced.
     * @param replacementParam The replacement for the given coeff.
     * @param factoryParam This factory will be used to create new nodes.
     * @param ringCParam this ring will be used for optimizations, may be null.
     */
    public CoeffSubstitutionVisitor(final C coeffParam, final C replacementParam,
            final GPolyFactory<C, V> factoryParam, final Semiring<C> ringCParam) {
        this.coeff = coeffParam;
        this.replacement = replacementParam;
        this.factory = factoryParam;
        this.ringC = ringCParam;
    }

    /**
     * Replace the coeff in both children and return the new times node.
     * @param t The TimesNode being visited.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return The new TimesNode where the coeff is substituted.
     */
    @Override
    public GPoly<C, V> caseTimesNode(final TimesNode<C, V> t, final GPoly<C, V> left, final GPoly<C, V> right) {
        final Pair<GPoly<C, V>, GPoly<C, V>> pair = this.computeConstants(left, right);
        return this.factory.times(pair.x, pair.y);
    }

    /**
     * Replace the coeff in both children and return the new plus node.
     * @param p The PlusNode being visited.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return The new PlusNode where the coeff is substituted.
     */
    @Override
    public GPoly<C, V> casePlusNode(final PlusNode<C, V> p, final GPoly<C, V> left, final GPoly<C, V> right) {
        final Pair<GPoly<C, V>, GPoly<C, V>> pair = this.computeConstants(left, right);
        return this.factory.plus(pair.x, pair.y);
    }

    /**
     * Replace the coeff in both children and return the new minus node.
     * @param m The MinusNode being visited.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return The new MinusNode where the coeff is substituted.
     */
    @Override
    public GPoly<C, V> caseMinusNode(final MinusNode<C, V> m, final GPoly<C, V> left, final GPoly<C, V> right) {
        final Pair<GPoly<C, V>, GPoly<C, V>> pair = this.computeConstants(left, right);
        return this.factory.minus(pair.x, pair.y);
    }

    /**
     * Replace the coeff in both children and return the new max node.
     * @param m The MaxNode being visited.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return The new MaxNode where the coeff is substituted.
     */
    @Override
    public GPoly<C, V> caseMaxNode(final MaxNode<C, V> m, final GPoly<C, V> left, final GPoly<C, V> right) {
        final Pair<GPoly<C, V>, GPoly<C, V>> pair = this.computeConstants(left, right);
        return this.factory.max(pair.x, pair.y);
    }

    /**
     * Replace the coeff in both children and return the new min node.
     * @param m The MinNode being visited.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return The new MinNode where the coeff is substituted.
     */
    @Override
    public GPoly<C, V> caseMinNode(final MinNode<C, V> m, final GPoly<C, V> left, final GPoly<C, V> right) {
        final Pair<GPoly<C, V>, GPoly<C, V>> pair = this.computeConstants(left, right);
        return this.factory.min(pair.x, pair.y);
    }

    /**
     * Replace the given coeff by the substitute, if it is attached to this
     * node.
     * @param c The ConcatNode being visited.
     * @return Some new node where the variable is substituted.
     */
    @Override
    public GPoly<C, V> caseConcatNode(final ConcatNode<C, V> c) {
        if (this.coeff.equals(c.getCoeff())) {
            return this.factory.concat(this.replacement, c.getVarPartNode());
        } else {
            // nothing to do here, the coeff was not found
            return c;
        }
    }

    /**
     * A min node is being visited. This is called before the children are
     * visited.
     * @param t Some TimesNode.
     */
    @Override
    public void fcaseMinNode(final MinNode<C, V> t) {
        // avoid exception
    }

    /**
     * A max node is being visited. This is called before the children are
     * visited.
     * @param t Some TimesNode.
     */
    @Override
    public void fcaseMaxNode(final MaxNode<C, V> t) {
        // avoid exception
    }

    /**
     * If any of the two polynomials represents a constant, replace the (complicated?) object by a simple object for the
     * constant. If the represented constant is 1 or 0, the factory may use this information to optimize when working
     * with the returned polynomials.
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
