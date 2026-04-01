package aprove.api.prooftree;

/**
 * Indicates that the export failed.
 */
public class ExportFailedException extends Exception {

    public ExportFailedException() {
        super();
    }

    public ExportFailedException(String message, Throwable cause) {
        super(message, cause);
    }

    public ExportFailedException(String message) {
        super(message);
    }

    public ExportFailedException(Throwable cause) {
        super(cause);
    }
}
