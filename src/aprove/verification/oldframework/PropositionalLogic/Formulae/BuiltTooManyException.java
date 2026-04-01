package aprove.verification.oldframework.PropositionalLogic.Formulae;

/**
 * To be thrown if a CountingFormulaFactory has built too many
 * formulae.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class BuiltTooManyException extends RuntimeException {

    public BuiltTooManyException() {
        super();
    }

    public BuiltTooManyException(String message) {
        super(message);
    }
}
