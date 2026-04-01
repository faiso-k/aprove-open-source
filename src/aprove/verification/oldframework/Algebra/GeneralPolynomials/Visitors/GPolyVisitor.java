/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Every implementation provides methods that will be called from the visited
 * object. The visitor's job is to collect information, return modified objects,
 * etc.
 * In a typical run the visitor is called with some root node x as the argument.
 * Then x.visit(this) is called, so that the object behind x knows where to
 * answer. Because x knows everything about itself, it will call the appropriate
 * method of the given visitor. So a PlusNode might call casePlusNode,
 * whereas a CoeffNode might call caseCoeffNode. The visitor then knows what
 * x is and can do its work. Additionally x will tell all its children to
 * contact the visitor. In the case where the visitor's result handling a
 * father node depends on the visitor's result on the children nodes, the
 * methods applyToLeft and applyToRight exist. Here the visitor will put the
 * result in a way that this is accessible by the visitor's method dealing with
 * the father node.
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 * @author cotto
 * @version $Id$
 */
public abstract class GPolyVisitor<C extends GPolyCoeff, V extends GPolyVar> {
    /**
     * Tell the given object to be visited.
     * @param visitable The object to be visited.
     * @return A visitable object where some operation is applied, depending on
     * the visitor used.
     */
     public GPoly<C, V> applyTo(final GPoly<C, V> visitable) {
         return visitable.visit(this);
     }

     /**
      * A concat node is being visited. This is called before the children are
      * visited (which a concat node does not have).
      * @param c Some ConcatNode.
      */
     public void fcaseConcatNode(
             final ConcatNode<C, V> c) { }

     /**
      * A concat node is being visited. This is called after the children were
      * visited (which a concat node does not have).
      * @param c Some ConcatNode.
      * @return Some new node depending on the visitor.
      */
     public GPoly<C, V> caseConcatNode(
             final ConcatNode<C, V> c) { return c; }

     /**
      * A plus node is being visited. This is called before the children are
      * visited.
      * @param p Some PlusNode.
      */
     public void fcasePlusNode(
             final PlusNode<C, V> p) { }

     /**
      * A plus node is being visited. This is called after the children were
      * visited.
      * @param p Some PlusNode.
      * @param left The possibly new left node.
      * @param right The possibly new right node.
      * @return Some new node depending on the visitor.
      */
     public GPoly<C, V> casePlusNode(
             final PlusNode<C, V> p,
             final GPoly<C, V> left,
             final GPoly<C, V> right) { return p; }

     /**
      * A minus node is being visited. This is called before the children are
      * visited.
      * @param m Some MinusNode.
      */
     public void fcaseMinusNode(
             final MinusNode<C, V> m) { }

     /**
      * A minus node is being visited. This is called after the children were
      * visited.
      * @param m Some MinusNode.
      * @param left The possibly new left node.
      * @param right The possibly new right node.
      * @return Some new node depending on the visitor.
      */
     public GPoly<C, V> caseMinusNode(
             final MinusNode<C, V> m,
             final GPoly<C, V> left,
             final GPoly<C, V> right) { return m; }

     /**
      * A times node is being visited. This is called before the children are
      * visited.
      * @param t Some TimesNode.
      */
     public void fcaseTimesNode(
             final TimesNode<C, V> t) { }


     /**
      * A min node is being visited. This is called before the children are
      * visited.
      * @param t Some TimesNode.
      */
     public void fcaseMinNode(
             final MinNode<C, V> t) {
         throw new UnsupportedOperationException("Min / max not yet implemented.");
     }

     /**
      * A max node is being visited. This is called before the children are
      * visited.
      * @param t Some TimesNode.
      */
     public void fcaseMaxNode(
             final MaxNode<C, V> t) {
         throw new UnsupportedOperationException("Min / max not yet implemented.");
     }

     /**
      * A minimum node is being visited. This is called after the children were
      * visited.
      * @param m Some MinNode.
      * @param left The possibly new left node.
      * @param right The possibly new right node.
      * @return Some new node depending on the visitor.
      */
     public GPoly<C, V> caseMinNode(
             final MinNode<C, V> m,
             final GPoly<C, V> left,
             final GPoly<C, V> right) { return m; }

     /**
      * A maximum node is being visited. This is called after the children were
      * visited.
      * @param m Some MaxNode.
      * @param left The possibly new left node.
      * @param right The possibly new right node.
      * @return Some new node depending on the visitor.
      */
     public GPoly<C, V> caseMaxNode(
             final MaxNode<C, V> m,
             final GPoly<C, V> left,
             final GPoly<C, V> right) { return m; }

     /**
      * A times node is being visited. This is called after the children were
      * visited.
      * @param t Some TimesNode.
      * @param left The possibly new left node.
      * @param right The possibly new right node.
      * @return A new node depending on the visitor.
      */
     public GPoly<C, V> caseTimesNode(
             final TimesNode<C, V> t,
             final GPoly<C, V> left,
             final GPoly<C, V> right) { return t; }
}
