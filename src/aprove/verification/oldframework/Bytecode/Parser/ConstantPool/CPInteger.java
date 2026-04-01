package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

/**
 * A class representing an integer entry in a constant pool of a Java class file.
 * @author Marc Brockschmidt
 */
public final class CPInteger implements CPEntry {
    /**
     * The integer constant stored in this entry.
     */
    private final int content;

    /**
     * Creates a new object representing an integer constant in a Java class file.
     * @param i the actual int to be represented.
     */
    public CPInteger(final int i) {
        this.content = i;
    }

    /**
     * @return the stored integer constant.
     */
    public int getInt() {
        return this.content;
    }

    /** @inheritDoc
     *  @return string representation of this object. */
    @Override
    public String toString() {
        return "" + this.content;
    }

    @Override
    public void writeTo(final DataOutputStream out) throws IOException {
        assert (false);
    }
}
