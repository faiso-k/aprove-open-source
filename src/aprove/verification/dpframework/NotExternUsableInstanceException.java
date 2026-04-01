package aprove.verification.dpframework;

/**
 * Thrown if an instance of an ExternUsable object cannot be converted
 * to string form.
 */
public class NotExternUsableInstanceException extends Exception {

    private static final long serialVersionUID = 1L;

    public NotExternUsableInstanceException() {
    }

    public NotExternUsableInstanceException(String msg) {
        super(msg);
    }

    public NotExternUsableInstanceException(String msg, Throwable cause) {
        super(msg, cause);
    }

    public NotExternUsableInstanceException(Throwable cause) {
        super(cause);
    }

}
