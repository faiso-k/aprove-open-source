package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

/**
 * A class representing a field or method name and type by two references
 * to the constant pool.
 * @author Marc Brockschmidt
 */
public final class CPNameAndTypeRef implements CPEntry {
    /** A reference to the constant pool, pointing to a raw Unicode string
     *  interpreted as name. */
    private final int nameRefIndex;

    /** A reference to the constant pool, pointing to a raw Unicode string
     *  interpreted as type descriptor. */
    private final int descriptorRefIndex;

    /**
     * Creates a new object representing name and type of some field or method
     * by two references to the constant pool.
     * @param nRefIndex A reference to the constant pool, pointing to a raw
     *  Unicode string interpreted as name.
     * @param dRefIndex A reference to the constant pool, pointing to a raw
     *  Unicode string interpreted as type descriptor.
     */
    public CPNameAndTypeRef(final int nRefIndex, final int dRefIndex) {
        this.nameRefIndex = nRefIndex;
        this.descriptorRefIndex = dRefIndex;
    }

    /** @return A reference to the constant pool, pointing to a raw Unicode
     *  string interpreted as name. */
    public int getNameRefIndex() {
        return this.nameRefIndex;
    }

    /** @return A reference to the constant pool, pointing to a raw Unicode
     *  string interpreted as type descriptor. */
    public int getDescriptorRefIndex() {
        return this.descriptorRefIndex;
    }

    /** @inheritDoc
     *  @return string representation of this object. */
    @Override
    public String toString() {
        return "Name at CP#" + this.nameRefIndex + " descriptor at CP#" + this.descriptorRefIndex;
    }

    @Override
    public void writeTo(final DataOutputStream out) throws IOException {
        assert (false);
    }
}
