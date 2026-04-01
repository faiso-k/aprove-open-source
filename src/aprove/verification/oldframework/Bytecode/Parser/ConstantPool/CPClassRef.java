package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * A class representing a class name in a constant pool of a Java class file by
 * holding a reference to a raw Unicode string holding the class name.
 * @author Marc Brockschmidt
 */
public final class CPClassRef implements CPEntry {
    /**
     * Index of the referenced raw Unicode string holding the class name.
     */
    private final int classRefIndex;

    /**
     * Creates a new object representing a class name in a constant pool of a
     * Java class file by holding a reference to a raw Unicode string holding
     * the class name.
     * @param index Index of the referenced raw Unicode string.
     */
    public CPClassRef(final int index) {
        this.classRefIndex = index;
    }

    /**
     * @return index of the referenced raw Unicode string holding the class name.
     */
    public int getClassRefIndex() {
        return this.classRefIndex;
    }

    /** @inheritDoc
     *  @return string representation of this object. */
    @Override
    public String toString() {
        return "Class name at CP#" + this.classRefIndex;
    }

    @Override
    public void writeTo(final DataOutputStream out) throws IOException {
        out.write(ClassFileParserConstants.CONSTANT_POOL_CLASS_REF_TAG);
        out.writeChar(this.classRefIndex);
    }
}
