package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

/**
 * A class representing a string reference entry in a constant pool of a Java class file.
 * @author Marc Brockschmidt
 */
public final class CPStringRef implements CPEntry {
    /**
     * Index of the referenced raw Unicode string.
     */
    private final int stringRefIndex;

    /**
     * Creates a new object representing a String reference entry in the constant pool
     * of a Java class file.
     * @param index Index of the referenced raw Unicode string.
     */
    public CPStringRef(final int index) {
        this.stringRefIndex = index;
    }

    /**
     * @return index of the referenced raw Unicode string.
     */
    public int getStringRefIndex() {
        return this.stringRefIndex;
    }

    /** @inheritDoc
     *  @return string representation of this object. */
    @Override
    public String toString() {
        return "String at CP#" + this.stringRefIndex;
    }

    @Override
    public void writeTo(final DataOutputStream out) throws IOException {
        assert (false);
    }
}
