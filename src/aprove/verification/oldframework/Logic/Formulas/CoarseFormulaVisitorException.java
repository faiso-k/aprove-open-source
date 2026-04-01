package aprove.verification.oldframework.Logic.Formulas;

import aprove.verification.oldframework.Exceptions.*;

public interface CoarseFormulaVisitorException<T> {

    /**
     * the truth value case
     */
    public T caseTruthValue(FormulaTruthValue truthvalFormula) throws InvalidPositionException;

    /**
     * the equation case
     */
    public T caseEquation(Equation eqFormula) throws InvalidPositionException;

    /**
     * the junctor formula case (not, and, or, impl, equiv). beware, psi may be
     * null (not-Junctor)
     */
    public T caseJunctorFormula(JunctorFormula jFormula) throws InvalidPositionException;

}
