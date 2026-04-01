package aprove.verification.oldframework.Logic.Formulas ;

/**
 *  a coarse formula visitor. coarse means it is not interested in
 *  knowing which junctor or which type of quantifier there actually is
 *  @author  Burak
 *  @version $Id$
 */

public interface CoarseFormulaVisitor<T> {
    /**
     * the truth value case
     */
    public T caseTruthValue( FormulaTruthValue truthvalFormula );

    /**
     * the equation case
     */
    public T caseEquation( Equation eqFormula );

    /**
     * the junctor formula case (not, and, or, impl, equiv).
     * beware, psi may be null (not-Junctor)
     */
    public T caseJunctorFormula( JunctorFormula jFormula );

}