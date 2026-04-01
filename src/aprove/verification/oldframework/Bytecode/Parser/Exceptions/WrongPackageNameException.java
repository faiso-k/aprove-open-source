package aprove.verification.oldframework.Bytecode.Parser.Exceptions;

import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * This exception is thrown, if we try to parse a file where the package name
 * does not match the expected package name.
 * @author cotto
 */
public class WrongPackageNameException extends ClassParseException {
    /**
     * A unique ID.
     */
    private static final long serialVersionUID = 5309388567211765135L;

    /**
     * Provide a readable string representation.
     * @param className the class name with the wrong package name
     * @param expected the package name we expected
     */
    public WrongPackageNameException(final ClassName className,
            final String expected) {
        super("The package name of " + className
            + " does not match the expected package name " + expected);
    }

}
