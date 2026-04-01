package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

public class CPMethodHandle implements CPEntry {

    private byte referenceKind;
    private short referenceIndex;

    public CPMethodHandle(byte referenceKind, short referenceIndex) {
        this.referenceKind = referenceKind;
        this.referenceIndex = referenceIndex;
    }

    public byte getReferenceKind() {
        return referenceKind;
    }

    public short getReferenceIndex() {
        return referenceIndex;
    }

    @Override
    public void writeTo(DataOutputStream out) throws IOException {
        assert false;
    }

}
