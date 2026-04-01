/*
 * Created on 04.09.2004
 *
 */
package aprove.verification.oldframework.Typing;

/**
 * Exception is throw if an typing error occurres
 * @author rabe
 */
public class TypingException extends RuntimeException {


    /**
     * Standard constructor
     */
    public TypingException() {
        super();
    }

    /**
     * Constructor supporting an exception message
     * @param message exception message
     */
    public TypingException(String message) {
        super(message);
    }

}
