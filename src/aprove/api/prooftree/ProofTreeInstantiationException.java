package aprove.api.prooftree;

/**
 * Indicates that the proof tree cannot be created.
 */
public class ProofTreeInstantiationException extends Exception {

    public ProofTreeInstantiationException() {
        super();
    }

    public ProofTreeInstantiationException(String message, Throwable cause) {
        super(message, cause);
    }

    public ProofTreeInstantiationException(String message) {
        super(message);
    }

    public ProofTreeInstantiationException(Throwable cause) {
        super(cause);
    }
}
