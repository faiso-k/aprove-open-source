package aprove.verification.oldframework.Bytecode.Parser.Exceptions;


/** An exception indicating that the first four byte of the parsed file don't match
 *  the magic number specified for class files.
 * @author Marc Brockschmidt
 */
public final class WrongMagicNumberException extends ClassParseException {
    /** Some UID used for serializing */
    private static final long serialVersionUID = -1517214817494728500L;

    /** An exception indicating that the first four byte of the parsed file
     *  don't match the magic number specified for class files.
     *  @param magicNumber The magic number found in the class file.
     */
    public WrongMagicNumberException(final int magicNumber) {
        super("Wrong magic number " + magicNumber);
    }
}
