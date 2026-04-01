package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

/**
 * A class representing a long entry in a constant pool of a Java class file.
 * @author Marc Brockschmidt
 */
public final class CPLong implements CPEntry {
    /**
     * The long constant stored in this entry.
     */
    private final long content;

    /**
     * Creates a new object representing a long constant in a Java class file.
     * @param l the actual long to be represented.
     */
    public CPLong(final long l) {
        this.content = l;
    }

    /**
     * @return the stored long constant.
     */
    public long getLong() {
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
