package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * A class representing a String entry in a constant pool of a Java class file.
 * @author Marc Brockschmidt
 */
public final class CPString implements CPEntry {
    /**
     * The string constant stored in this entry.
     */
    private final String content;

    /**
     * Creates a new object representing a string constant in a Java class file.
     * @param c the actual string to be represented.
     */
    public CPString(final String c) {
        this.content = c;
    }

    /**
     * @return the stored string constant.
     */
    public String getString() {
        return this.content;
    }

    /** @inheritDoc
     *  @return string representation of this object. */
    @Override
    public String toString() {
        return this.content;
    }

    @Override
    public void writeTo(final DataOutputStream out) throws IOException {
        out.write(ClassFileParserConstants.CONSTANT_POOL_UTF8_TAG);
        out.writeUTF(this.content);
    }
}
