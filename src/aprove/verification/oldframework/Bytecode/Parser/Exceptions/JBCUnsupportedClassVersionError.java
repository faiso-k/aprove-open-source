package aprove.verification.oldframework.Bytecode.Parser.Exceptions;

/**
 * An exception indicating an unsupported version of the class file.
 * @author Carsten Otto
 */
public final class JBCUnsupportedClassVersionError extends ClassParseException {
    /**
     * A unique ID.
     */
    private static final long serialVersionUID = -91215632311077834L;

    /**
     * An exception indicating an unsupported version of the class file.
     * @param major the major version number
     * @param minor the minor version number
     */
    public JBCUnsupportedClassVersionError(final int major, final int minor) {
        super("Unsupported version number: " + major + "." + minor);
    }
}
