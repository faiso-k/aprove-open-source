/**
 * @author cotto
 * @version $Id$
 */
package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import immutables.*;

/**
 * A VarPartNode is a product of variables, e.g. x*y*z*z = xyz^2.
 *
 * @param <V> The type of the variables.
 */
public class VarPartNode<V extends GPolyVar> implements Immutable, Exportable {
    /**
     * If this is a leaf, then store the represented variable (maybe null for
     * the variable part representing 1).
     */
    private final V var;

    /**
     * Store the variables that occur below this node (or in this node).
     */
    private ImmutableSet<V> variables;

    /**
     * Store the variables that occur in or below this node together with
     * the number of their occurrences (i.e. with their exponents).
     */
    private ImmutableMap<V, Integer> variablesWithExponents;

    /**
     * If this node combines two VarPartNodes, store the children here.
     * Left child.
     */
    private final VarPartNode<V> left;

    /**
     * Right child.
     */
    private final VarPartNode<V> right;

    /**
     * Store the monomial here if computed. This depends on the monoid used
     * to multiply the single variables.
     */
    private final Map<CMonoid<GMonomial<V>>, GMonomial<V>> monomial;

    /**
     * Create the variable part representing 1.
     */
    VarPartNode() {
        this.left = null;
        this.right = null;
        this.var = null;
        this.monomial = new HashMap<>();
    }

    /**
     * Create the variable part representing a single variable.
     * @param varParam The variable being represented.
     */
    VarPartNode(final V varParam) {
        if (Globals.useAssertions) {
            assert (varParam != null);
        }
        this.left = null;
        this.right = null;
        this.var = varParam;
        this.monomial = new HashMap<>();
    }

    /**
     * Create the variable part that represents the product of all the given
     * variables (each with exponent 1).
     * @param vars The variables to be used to create the var part node.
     */
    VarPartNode(final Collection<V> vars) {
        if (Globals.useAssertions) {
            assert (vars != null);
        }
        final int size = vars.size();
        if (size == 0) {
            this.left = null;
            this.right = null;
            this.var = null;
        } else if (size == 1) {
            this.left = null;
            this.right = null;
            this.var = vars.iterator().next();
        } else {
            final List<V> list = new ArrayList<>(vars);
            List<V> subset = new ArrayList<>(size / 2);
            for (int i = 0; i < size / 2; i++) {
                subset.add(list.get(i));
            }
            this.left = new VarPartNode<>(subset);
            subset = new ArrayList<>(size - size / 2);
            for (int i = size / 2; i < size; i++) {
                subset.add(list.get(i));
            }
            this.right = new VarPartNode<>(subset);
            this.var = null;
        }
        this.monomial = new HashMap<>();
    }

    /**
     * Create a VarPartNode that combines two other VarPartNodes.
     * @param leftParam The VarPartNode which is the left child.
     * @param rightParam The VarPartNode which is the right child.
     */
    VarPartNode(final VarPartNode<V> leftParam, final VarPartNode<V> rightParam) {
        if (Globals.useAssertions) {
            assert (leftParam != null);
            assert (rightParam != null);
        }
        this.left = leftParam;
        this.right = rightParam;
        this.var = null;
        this.monomial = new HashMap<>();
    }

    /**
     * Create a new VarPartNode containing the vars from the given monomial.
     * @param monomial Some monomial.
     */
    public static <V extends GPolyVar> VarPartNode<V> fromMonomial(final GMonomial<V> monomial) {

        final List<V> vars = new ArrayList<>();
        for (final Map.Entry<V, BigInteger> entry : monomial.getExponents().entrySet()) {
            final V var = entry.getKey();
            final int exponent = entry.getValue().intValue();
            for (int i = 0; i < exponent; i++) {
                vars.add(var);
            }
        }
        return new VarPartNode<>(vars);
    }

    /**
     * @param varParam The variable to look for.
     * @return true iff the DAG starting at this node somewhere contains the
     * given variable.
     */
    public synchronized boolean containsVariable(final V varParam) {
        if (this.variables == null) {
            this.calculateVariables();
        }
        return this.variables.contains(varParam);
    }

    /**
     * @return the set of all variables contained in or below this node.
     */
    public synchronized ImmutableSet<V> getVariables() {
        if (this.variables == null) {
            this.calculateVariables();
        }
        return this.variables;
    }

    /**
     * @return all variables contained in or below this node, together
     * with their exponents.
     */
    public synchronized ImmutableMap<V, Integer> getVariablesWithExponents() {
        if (this.variablesWithExponents == null) {
            this.calculateVariablesWithExponents();
        }
        return this.variablesWithExponents;
    }

    /**
     * Fill the variables cache.
     */
    private synchronized void calculateVariables() {
        if (Globals.useAssertions) {
            assert (this.variables == null);
        }
        if (this.var != null) {
            final Set<V> temp = Collections.singleton(this.var);
            this.variables = ImmutableCreator.create(temp);
        } else if (this.left != null && this.right != null) {
            final Set<V> temp = new LinkedHashSet<>(this.left.getVariables());
            temp.addAll(this.right.getVariables());
            this.variables = ImmutableCreator.create(temp);
        } else {
            this.variables = ImmutableCreator.create(Collections.<V>emptySet());
        }
    }

    /**
     * Fill the variablesWithExponents cache.
     */
    private synchronized void calculateVariablesWithExponents() {
        if (Globals.useAssertions) {
            assert (this.variablesWithExponents == null);
        }
        if (this.var != null) {
            final Map<V, Integer> temp = Collections.singletonMap(this.var, 1);
            this.variablesWithExponents = ImmutableCreator.create(temp);
        } else if (this.left != null && this.right != null) {
            final Map<V, Integer> temp = new LinkedHashMap<>(this.left.getVariablesWithExponents());
            final Map<V, Integer> rightMap = this.right.getVariablesWithExponents();
            for (final V currentVar : rightMap.keySet()) {
                final Integer leftOccs = temp.get(currentVar);
                if (leftOccs == null) {
                    temp.put(currentVar, rightMap.get(currentVar));
                } else {
                    temp.put(currentVar, leftOccs + rightMap.get(currentVar));
                }
            }
            this.variablesWithExponents = ImmutableCreator.create(temp);
        } else {
            this.variablesWithExponents = ImmutableCreator.create(Collections.<V, Integer>emptyMap());
        }
    }

    /**
     * Returns the sum of all exponents. This is the same as the number of
     * factors if you write this node as a flat product (using only
     * multiplication, without exponents).
     */
    public synchronized int length() {
        if (this.variablesWithExponents == null) {
            this.calculateVariablesWithExponents();
        }
        int result = 0;
        for (final Map.Entry<V, Integer> entry : this.variablesWithExponents.entrySet()) {
            result += entry.getValue();
        }
        return result;
    }

    /**
     * @return true iff at least one variable exists in this DAG.
     */
    public synchronized boolean containsVariable() {
        if (this.variables == null) {
            this.calculateVariables();
        }
        return this.variables.size() > 0;
    }

    /**
     * @return some readable string representation.
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        if (this.var != null) {
            sb.append(this.var.toString());
        } else {
            if (this.left != null && this.right != null) {
                sb.append(this.left.toString());
                sb.append(this.right.toString());
            }
        }
        return sb.toString();
    }

    /**
     * @return the variable.
     */
    public V getVar() {
        return this.var;
    }

    /**
     * @param monoid This monoid defines how the monomial looks like.
     * @return the monomial defined by the given monoid.
     */
    protected GMonomial<V> getMonomial(final CMonoid<GMonomial<V>> monoid) {
        if (Globals.useAssertions) {
            assert (this.monomial.containsKey(monoid));
        }
        return this.monomial.get(monoid);
    }

    /**
     * @return true iff the monomial for the given monoid already is calculated.
     * @param monoid The monoid defining the monomial.
     */
    protected boolean hasMonomial(final CMonoid<GMonomial<V>> monoid) {
        return this.monomial.containsKey(monoid);
    }

    /**
     * Put some value in the monomial map storing the flat representations.
     * @param monoid The monoid that was used to calculate the representation.
     * @param mon The monomial.
     */
    protected void putMonomial(final CMonoid<GMonomial<V>> monoid, final GMonomial<V> mon) {
        if (Globals.useAssertions) {
            assert (this.monomial.get(monoid) == null);
        }
        this.monomial.put(monoid, mon);
    }

    /**
     * Visit this node and the two children nodes, if present.
     * @param visitor The visitor visiting this object.
     * @return some visitable object defined by the visitor.
     */
    public VarPartNode<V> visit(final VarPartNodeVisitor<V> visitor) {
        visitor.fcaseVarPartNode(this);
        VarPartNode<V> newLeft = null;
        VarPartNode<V> newRight = null;
        if (this.left != null) {
            newLeft = visitor.applyTo(this.left);
        }
        if (this.right != null) {
            newRight = visitor.applyTo(this.right);
        }
        return visitor.caseVarPartNode(this, newLeft, newRight);
    }

    /**
     * @return true iff this node contains a variable or represents the 1
     * element.
     */
    public boolean isLeaf() {
        return this.var != null || (this.left == null && this.right == null);
    }

    /**
     * @return true iff this node represents the 1 element
     */
    public boolean isOne() {
        return this.var == null && this.left == null && this.right == null;
    }

    /**
     * @return the left child.
     */
    public VarPartNode<V> getLeft() {
        return this.left;
    }

    /**
     * @return the right child.
     */
    public VarPartNode<V> getRight() {
        return this.right;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        if (this.var != null) {
            sb.append(this.var.export(o));
        } else {
            if (this.left != null && this.right != null) {
                sb.append(this.left.export(o));
                sb.append(this.right.export(o));
            }
        }
        return sb.toString();
    }

}
