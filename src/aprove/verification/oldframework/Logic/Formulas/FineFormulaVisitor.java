package aprove.verification.oldframework.Logic.Formulas ;


/** a fine formula visitor. fine means it is interested in
 *  knowing which junctor or which type of quantifier there actually is
 *  @author  Burak
 *  @version $Id$
 */

public interface FineFormulaVisitor<T>
{
    /** the truth value case
     */
    public T caseTruthValue( FormulaTruthValue truthvalFormula );

    /** the equation case
     */
    public T caseEquation( Equation phi );

    /** the negated formula case
     */
    public T caseNot( Not notFormula );

    /** the "phi and psi" case
     */
    public T caseAnd( And andFormula );

    /** the "phi or psi" case
     */
    public T caseOr( Or orFormula );

    /** the "from phi follows psi" case
     */
    public T caseImplication( Implication implFormula );

    /** the "phi is equiv. to psi" case
     */
    public T caseEquivalence( Equivalence equivFormula );
}
