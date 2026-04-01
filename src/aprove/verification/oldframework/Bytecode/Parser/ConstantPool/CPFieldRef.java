package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

/**
 * A class representing a class or interface field using two references to
 * the constant pool.
 * @author Marc Brockschmidt
 */
public final class CPFieldRef implements CpMemberRef {
    /** A reference to a constant pool entry describing a class. */
    private final int classRefIndex;
    /** A reference to a constant pool entry describing name and type of this field. */
    private final int fieldNameAndTypeRefIndex;

    /**
     * Creates a new object representing a class or interface field.
     * @param cRefIndex The index to the constant pool entry describing the class.
     * @param fRefIndex The index to the constant pool entry describing name and type of
     *  the field.
     */
    public CPFieldRef(final int cRefIndex, final int fRefIndex) {
        this.classRefIndex = cRefIndex;
        this.fieldNameAndTypeRefIndex = fRefIndex;
    }

    /**
     * @return A reference to a constant pool entry describing a class.
     */
    @Override
    public int getClassIndex() {
        return this.classRefIndex;
    }

    /**
     * @return A reference to a constant pool entry describing name and type of this field.
     */
    @Override
    public int getNameAndTypeRefIndex() {
        return this.fieldNameAndTypeRefIndex;
    }

    /** @inheritDoc
     *  @return string representation of this object. */
    @Override
    public String toString() {
        return "Class at CP#" + this.classRefIndex + " field at CP#" + this.fieldNameAndTypeRefIndex;
    }

    @Override
    public void writeTo(final DataOutputStream out) throws IOException {
        assert (false);
    }
}
