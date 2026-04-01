package immutables;

/**
 * To be thrown whenever one of the create methods of ImmutableCreator is
 * called with an instance for which there is no corresponding immutable class.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class NoCorrespondingImmutableClassException extends RuntimeException {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 1L;

    /**
     * @param message The exception's message.
     */
    public NoCorrespondingImmutableClassException(String message) {
        super(message);
    }

}
