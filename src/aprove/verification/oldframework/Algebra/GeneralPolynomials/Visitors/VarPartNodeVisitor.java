/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Every implementation of this visitor will be used to do some operation on the
 * variables representing in the DAG behind some variable part node. During
 * computation the method fcaseVarPartNode() will be called whenever some var
 * part node is visited, after that the children will be visited and in the end
 * caseVarPartNode() will be called. Traversal can be stopped by setting the
 * stop variable.
 * @param <V> The type of the variables.
 * @author cotto
 * @version $Id$
 */
public abstract class VarPartNodeVisitor<V extends GPolyVar> {
    /**
     * Should the visitor stop?
     */
    private boolean stop;

    /**
     * Tell the given object to be visited if this visitor is not stopped.
     * @param visitable The object to be visited.
     * @return A VarPartNode where some operation is applied, depending on
     * the visitor used.
     */
     public VarPartNode<V> applyTo(final VarPartNode<V> visitable) {
         if (this.stop) {
             return visitable;
         } else {
             return visitable.visit(this);
         }
     }

     /**
      * Stop traversing.
      */
     protected void setStop() {
         this.stop = true;
     }

     /**
      * A varpart node is being visited. This is called before the children are
      * visited.
      * @param v Some VarPartNode.
      */
     public void fcaseVarPartNode(
             final VarPartNode<V> v) { }

     /**
      * A varpart node is being visited. This is called after the children were
      * visited.
      * @param v Some VarPartNode.
      * @param leftChild The left child.
      * @param rightChild The right child.
      * @return a VarPartNode depending on the visitor.
      */
     public VarPartNode<V> caseVarPartNode(
             final VarPartNode<V> v,
             final VarPartNode<V> leftChild,
             final VarPartNode<V> rightChild) { return v; }
}
