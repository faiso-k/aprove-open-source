package aprove.input.Programs.intProg;

import org.antlr.runtime.*;

/**
 * Exception thrown by the C Integer Program parser. Must be a runtime exception to be thrown by the reportError method.
 * @author cryingshadow
 * @version $Id$
 */
@SuppressWarnings("serial")
public class IntProgParseException extends RuntimeException {

    /**
     * @param e The recognition exception to throw from the reportError method.
     */
    public IntProgParseException(RecognitionException e) {
        super(e);
    }

}
