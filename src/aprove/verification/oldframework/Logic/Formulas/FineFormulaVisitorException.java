package aprove.verification.oldframework.Logic.Formulas ;

import aprove.verification.oldframework.Exceptions.*;

/**
 *  a fine formula visitor. fine means it is interested in
 *  knowing which junctor or which type of quantifier there actually is
 *  @author  dickmeis
 *  @version $Id$
 */

public interface FineFormulaVisitorException<T>
{
    /** the truth value case
     */
    public T caseTruthValue( FormulaTruthValue truthvalFormula ) throws InvalidPositionException;

    /** the equation case
     */
    public T caseEquation( Equation phi ) throws InvalidPositionException;

    /** the negated formula case
     */
    public T caseNot( Not notFormula ) throws InvalidPositionException;

    /** the "phi and psi" case
     */
    public T caseAnd( And andFormula ) throws InvalidPositionException;

    /** the "phi or psi" case
     */
    public T caseOr( Or orFormula ) throws InvalidPositionException;

    /** the "from phi follows psi" case
     */
    public T caseImplication( Implication implFormula ) throws InvalidPositionException;

    /** the "phi is equiv. to psi" case
     */
    public T caseEquivalence( Equivalence equivFormula ) throws InvalidPositionException;
}
