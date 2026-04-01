/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Walk through the VarPartNodes and replace every occurrence of the given
 * variable by the given VarPartNode (maybe 1?).
 * @param <V> The type of the variables.
 * @author cotto
 * @version $Id$
 */
public class VariableReplacer<V extends GPolyVar> extends VarPartNodeVisitor<V> {
    /**
     * Store how often the variable was replaced.
     */
    private final Map<V, BigInteger> numbers = new DefaultValueMap<>(BigInteger.ZERO);

    /**
     * The variables that should be replaced.
     */
    private final Set<V> variables;

    /**
     * The varpart node that should be the replacement for all varpart nodes
     * containing one of the given variables.
     */
    private final VarPartNode<V> replacement;

    /**
     * Use this factory to create altered nodes.
     */
    private final GPolyFactory<?, V> factory;

    /**
     * Replace all occurences of the given variables by the given replacement
     * varpart.
     * @param variablesParam The variables to be replaced.
     * @param replacementParam The replacement.
     * @param factoryParam This factory will be used to generate altered nodes.
     */
    public VariableReplacer(final Set<V> variablesParam, final VarPartNode<V> replacementParam,
            final GPolyFactory<?, V> factoryParam) {
        this.variables = variablesParam;
        this.replacement = replacementParam;
        this.factory = factoryParam;
    }

    /**
     * @return the map giving information how often the variables were replaced.
     */
    public Map<V, BigInteger> getNumbers() {
        return this.numbers;
    }

    /**
     * Increment the corresponding counter, if the variable was found.
     * If this is not a leaf in the DAG then take care of (possibly) changed
     * children.
     * @param v The VarPartNode currently being visited.
     * @param left The left child.
     * @param right The right child.
     * @return A VarPartNode where all occurrences of the variables are
     * replaced.
     */
    @Override
    public VarPartNode<V> caseVarPartNode(final VarPartNode<V> v, final VarPartNode<V> left, final VarPartNode<V> right) {
        final V var = v.getVar();
        if (var == null) {
            // v is a node holding two varparts together.
            // because these might have changed, create a new node holding
            // the new versions. These possibly new nodes were stored in the
            // factory using applyToLeft and applyToRight.
            return this.factory.times(left, right);
        } else if (this.variables.contains(var)) {
            this.numbers.put(var, this.numbers.get(var).add(BigInteger.ONE));
            return this.replacement;
        } else {
            return v;
        }
    }
}
