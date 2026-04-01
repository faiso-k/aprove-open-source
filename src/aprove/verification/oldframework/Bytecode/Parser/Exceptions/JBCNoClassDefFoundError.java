package aprove.verification.oldframework.Bytecode.Parser.Exceptions;

import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * This exception is thrown if we analyze a class file with a name that differs
 * from the file name.
 * @author cotto
 */
public class JBCNoClassDefFoundError extends ClassParseException {
    /**
     * A unique ID.
     */
    private static final long serialVersionUID = -8136515838987231852L;

    /**
     * This exception is thrown if we analyze a class file with a name that
     * differs from the file name.
     * @param expectedName the expected name
     * @param parsedName the name we parsed
     */
    public JBCNoClassDefFoundError(final ClassName expectedName,
            final String parsedName) {
        super("The parsed name " + parsedName
            + " does not match the expected name " + expectedName);
    }

}
