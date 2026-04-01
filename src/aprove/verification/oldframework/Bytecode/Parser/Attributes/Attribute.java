package aprove.verification.oldframework.Bytecode.Parser.Attributes;

/**
 * Representation of raw, unparsed Java Bytecode class file attributes.
 *
 * @author Marc Brockschmidt
 */
public class Attribute {
    /** The attribute's name. */
    private final String attributeName;

    /** a byte array containing the unparsed attribute data. */
    private final byte[] unparsedData;

    /**
     * Create a new unparsed attribute. All information is saved for later use,
     * but we don't actually do anything with it.
     * @param attrName name of this attribute.
     * @param data a byte array containing the unparsed attribute data.
     */
    public Attribute(final String attrName, final byte[] data) {
        this.attributeName = attrName;
        this.unparsedData = data;
    }

    /**
     * @return the attribute's name.
     */
    public String getAttributeName() {
        return this.attributeName;
    }

    /**
     * @return a byte array containing the unparsed attribute data.
     */
    public byte[] getUnparsedData() {
        return this.unparsedData;
    }
}
