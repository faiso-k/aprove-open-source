package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

/**
 * A class representing a float entry in a constant pool of a Java class file.
 * @author Marc Brockschmidt
 */
public final class CPFloat implements CPEntry {
    /**
     * The float constant stored in this entry.
     */
    private final float content;

    /**
     * Creates a new object representing a float constant in a Java class file.
     * @param f the actual float value to be represented.
     */
    public CPFloat(final float f) {
        this.content = f;
    }

    /**
     * @return the stored float constant.
     */
    public float getFloat() {
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
