package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

/**
 * This exception is thrown when we ask for an position, but it is not available
 * in the state (e.g. because of abstract data).
 * @author cotto
 */
public final class PositionDoesNotExistException extends Exception {
    /**
     * We just need a singleton.
     */
    public static final PositionDoesNotExistException INSTANCE = new PositionDoesNotExistException();

    /**
     * Some UID.
     */
    private static final long serialVersionUID = 1L;

    /**
     * Just create a single instance.
     */
    private PositionDoesNotExistException() {

    }

}
