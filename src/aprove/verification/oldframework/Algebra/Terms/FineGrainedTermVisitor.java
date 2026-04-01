package aprove.verification.oldframework.Algebra.Terms;




/** Term visitor objects that need to know whether a function application is
 *  a constructor app or a def function app must implement this interface
 *  @author Burak
 *  @version $Id$
 */

public interface FineGrainedTermVisitor<T>
{
    /** the constructor application case
     */
    public T caseConstructorApp( ConstructorApp cterm );
    /** the def function application case
     */
    public T caseDefFunctionApp( DefFunctionApp fterm );

    public T caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication);

    /** the variable case
     */
    public T caseVariable( AlgebraVariable v );

}
