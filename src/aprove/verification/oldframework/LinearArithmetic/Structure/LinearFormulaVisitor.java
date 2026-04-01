package aprove.verification.oldframework.LinearArithmetic.Structure ;


/** a fine formula visitor. fine means it is interested in
 *  knowing which junctor or which type of quantifier there actually is
 *  @author  Burak
 *  @version $Id
 */

public interface LinearFormulaVisitor<T>
{
    public T caseTruthValue( TruthValueLinearFormula truthvalue );

    public T caseLinearConstraint( LinearConstraint linearConstraint );

    public T caseModuloLinearFormula( ModuloLinearFormula moduloLinearFormula);

    public T caseAllQuantifiedLinearFormula( AllQuantifiedLinearFormula allLinearFormula);

    public T caseExistentialQuantifiedLinearFormula( ExistentialQuantifiedLinearFormula existentialLinearFormula);

    public T caseNot( NotLinearFormula not );

    public T caseAnd( AndLinearFormula and );

    public T caseOr( OrLinearFormula or );

}
