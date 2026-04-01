package aprove.verification.oldframework.Exceptions;

/**
 * @author Matthias Sondermann
 * @version $Id$
 */
public class NotYetHandledException extends RuntimeException {

    private static final long serialVersionUID = 1L;

    public NotYetHandledException(String message) {
        super(message);
    }
}
