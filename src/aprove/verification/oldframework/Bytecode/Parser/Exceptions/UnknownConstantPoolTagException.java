package aprove.verification.oldframework.Bytecode.Parser.Exceptions;


/** An exception indicating an unknown tag used to identify a constant pool entry.
 * @author Marc Brockschmidt
 */
public final class UnknownConstantPoolTagException extends ClassParseException {
    /** Some UID used for serializing */
    private static final long serialVersionUID = 2681860448940199504L;

    /** An exception indicating an unknown tag used to identify a constant pool entry.
     *  @param entryNumber number of the constant pool entry with the unknown tag.
     *  @param tag the unknown tag
     */
    public UnknownConstantPoolTagException(final int entryNumber, final int tag) {
        super("Constant pool entry #" + entryNumber + " has unknown tag " + tag
            + "!");
    }
}
