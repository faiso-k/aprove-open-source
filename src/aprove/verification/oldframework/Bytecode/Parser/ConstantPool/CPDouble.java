package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

/**
 * A class representing a double entry in a constant pool of a Java class file.
 * @author Marc Brockschmidt
 */
public final class CPDouble implements CPEntry {
    /**
     * The double constant stored in this entry.
     */
    private final double content;

    /**
     * Creates a new object representing a double constant in a Java class file.
     * @param d the actual double value to be represented.
     */
    public CPDouble(final double d) {
        this.content = d;
    }

    /**
     * @return the stored double constant.
     */
    public double getDouble() {
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
