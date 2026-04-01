package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

/**
 * A class representing a class method using two references to the constant
 * pool.
 * @author Marc Brockschmidt
 */
public final class CPMethodRef implements CpMemberRef {
    /** A reference to a constant pool entry describing a class. */
    private final int classRefIndex;
    /** A reference to a constant pool entry describing name and type of this method. */
    private final int methodNameAndTypeRefIndex;

    /**
     * Creates a new object representing a class method.
     * @param cRefIndex The index to the constant pool entry describing the class.
     * @param mRefIndex The index to the constant pool entry describing name and type of
     *  the method.
     */
    public CPMethodRef(final int cRefIndex, final int mRefIndex) {
        this.classRefIndex = cRefIndex;
        this.methodNameAndTypeRefIndex = mRefIndex;
    }

    /**
     * @return A reference to a constant pool entry describing a class.
     */
    @Override
    public int getClassIndex() {
        return this.classRefIndex;
    }

    /**
     * @return A reference to a constant pool entry describing name and type of this method.
     */
    @Override
    public int getNameAndTypeRefIndex() {
        return this.methodNameAndTypeRefIndex;
    }

    /** @inheritDoc
     *  @return string representation of this object. */
    @Override
    public String toString() {
        return "Class at CP#" + this.classRefIndex + " method at CP#" + this.methodNameAndTypeRefIndex;
    }

    @Override
    public void writeTo(final DataOutputStream out) throws IOException {
        assert (false);
    }
}
