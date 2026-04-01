package aprove.verification.oldframework.Algebra.Terms;


/** This interface defines which methods a coarsely grained term visitor,
 *  i.e. one that only discriminates between variables and function
 *  applications, has to implement.
 *  <p>
 *  Only implement this interface if you make a shallow visit to the term
 *  or there is no abstract descending implementation that suits your needs.
 *  In most cases you will want to extend CoarseGrainedDepthFirstTermVisitor.
 *  @author Burak Emir
 *  @version $Id$
 */

public interface CoarseGrainedTermVisitor<T> {

    public T caseVariable(AlgebraVariable v);

    public T caseFunctionApp(AlgebraFunctionApplication f);

}
