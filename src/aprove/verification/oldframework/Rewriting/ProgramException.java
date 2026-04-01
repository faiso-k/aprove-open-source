package aprove.verification.oldframework.Rewriting;

/** Thrown when trying to add already defined symbols.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class ProgramException extends Exception {

    public ProgramException(String  message) {
        super(message);
    }

}
