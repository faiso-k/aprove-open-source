package aprove.verification.oldframework.PropositionalLogic;

/**
 * Interface for instances of FormulaFactory that autodestruct in a
 * BuitTooManyException as soon as the number of build subformulae
 * exceeds a certain limit.
 *
 * @author Carsten Fuhs
 */
public interface CountingFormulaFactory<T> extends FormulaFactory<T> {}
