package aprove.verification.oldframework.Algebra.Terms;

import aprove.verification.oldframework.Exceptions.*;

public interface CoarseGrainedTermVisitorException<T> {

     public T caseVariable(AlgebraVariable v) throws InvalidPositionException;

     public T caseFunctionApp(AlgebraFunctionApplication f) throws InvalidPositionException;

}
