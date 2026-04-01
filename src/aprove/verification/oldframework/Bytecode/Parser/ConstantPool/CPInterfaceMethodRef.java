package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

/**
 * A class representing an interface method using two references to the constant
 * pool.
 * @author Marc Brockschmidt
 */
public final class CPInterfaceMethodRef implements CpMemberRef {
    /** A reference to a constant pool entry describing an interface. */
    private final int interfaceRefIndex;
    /** A reference to a constant pool entry describing name and type of this method. */
    private final int methodNameAndTypeRefIndex;

    /**
     * Creates a new object representing an interface method.
     * @param iRefIndex The index to the constant pool entry describing the interface.
     * @param mRefIndex The index to the constant pool entry describing name and type of
     *  the method.
     */
    public CPInterfaceMethodRef(final int iRefIndex, final int mRefIndex) {
        this.interfaceRefIndex = iRefIndex;
        this.methodNameAndTypeRefIndex = mRefIndex;
    }

    /**
     * @return A reference to a constant pool entry describing an interface.
     */
    @Override
    public int getClassIndex() {
        return this.interfaceRefIndex;
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
        return "Interface at CP#" + this.interfaceRefIndex + " method at CP#" + this.methodNameAndTypeRefIndex;
    }

    @Override
    public void writeTo(final DataOutputStream out) throws IOException {
        assert (false);
    }
}
